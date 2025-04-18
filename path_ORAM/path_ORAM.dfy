include "server.dfy"
include "math.dfy"

// Minimum size requirement for ORAM to be secure
const MIN_BLOCKS: nat := 2
// Option type
datatype option<T> = Some(value: T) | None


class PathORAM {
    // Core ORAM parameters
    var N: nat          // Total number of blocks
    var Z: nat          // Bucket size (i.e., how many blocks in each tree node)
    var L: nat          // Height of the tree
    var numLeaves: nat  // Number of leaves
    var treeSize: nat   // Total size of the tree
    
    // Data structures
    var tree: Database         // Database on server storing buckets in tree structure
    var posMap: array<nat>     // Position map: block index -> leaf bucket index
    var stash: map<nat, string>  // Temporary client storage for blocks (maps block address to block data)

    // Constructor
    constructor(numBlocks: nat, bucketSize: nat)
        requires numBlocks >= MIN_BLOCKS  // At least 2 blocks required
        requires bucketSize >= 1
        ensures N == numBlocks
        ensures fresh(tree)
        ensures L >= 1  // Tree has at least one level
        ensures numLeaves >= 1
        ensures treeSize >= 1
        ensures posMap.Length == N
    {
        N := numBlocks;
        Z := bucketSize;
        tree := new Database(1, 1);  // (Dafny requires an initialization before "new;")

        new;  // (See "Two-phase constructors" in the Dafny documentation for explanation)

        L := Math.CeilLog2(N);
        numLeaves := Math.Pow2(L);
        treeSize := 2 * numLeaves - 1;
        
        // Initialize data structures
        tree := new Database(treeSize, Z);
        posMap := new nat[N]; // TODO
        stash := map[];
    }


    // Select the index of a leaf node nondeterministically
    // (Ideally this would be uniformly at random, but the implementation below doesn't do this)
    method {:private} RandomLeaf() returns (leaf: nat)
        requires treeSize >= 1
        ensures IsLeaf(leaf)
    {
        assert IsLeaf(treeSize-1);
        leaf :| IsLeaf(leaf);
    }

    // Returns sequence of indices of the nodes from the root to the input node
    // When called on a leaf x, gives the value of P(x,l) from the paper for each l in {0,...,L}
    function {:private} PathNodes(node: nat) : (path: seq<nat>)
        requires 0 <= node < treeSize
        ensures |path| == CorrectPathLength(node)
        ensures IsLeaf(node) ==> |path| == L + 1  // Path length for leaf nodes is tree height + 1
        ensures |path| > 0
        ensures path[0] == 0     // First node is root
        ensures forall i :: 0 <= i < |path|-1 ==> 
            path[i+1] == 2 * path[i] + 1 || path[i+1] == 2 * path[i] + 2
        reads this`treeSize
    {
        LemmaLeafCorrectPathLength(node);
        // assert IsLeaf(node) ==> Math.FloorLog2(node+1) == L;
        if node == 0 then [0]
        else PathNodes((node - 1) / 2) + [node]
    }

    // This is the Access function (Figure 1) from the Path ORAM paper
    // We refer to the line numbers from the paper in the comments here
    method Access(op: string, addr: nat, newData: option<string>) returns (data: option<string>)
        requires op == "R" || op == "W"
        requires 0 <= addr < N
        requires posMap.Length == N
        requires forall i :: 0 <= i < N ==> IsLeaf(posMap[i])
        requires op == "R" ==> newData.None?
        requires op == "W" ==> newData.Some?
        modifies this.posMap, this`stash, this.tree, this.tree`accessLog
        // ensures posMap.Length == N
        // ensures forall i :: 0 <= i < N ==> IsLeaf(posMap[i])
        // ensures op == "W" ==> block in data && data[block] == newData

        // ORAM correctness invariants:

        // - posMap maps each block to a uniformly random leaf node.
        //   TODO
        //     This is a claim about a probability distribution --
        //     I'm not sure how to express this.
        //     A previous version had "ensures block in posMap" and
        //     "ensures posMap[block] != old(posMap[block])", which do not capture this idea.
        //     The former is always true (blocks always have a mapping), and
        //     the latter is false: the new mapping is allowed to be the same as the old one,
        //     because you choose uniformly at random.

        // - The block is either in a bucket along the path to the leaf or in the stash.
        ensures (posMap[addr] in PathNodes(posMap[addr])) || (addr in stash.Keys)

        // - Whenever a block is read from the server, the entire path
        //   to the mapped leaf is read into the stash, the requested block
        //   is remapped to another leaf, and then the path that was just
        //   read is written back to the server. When the path is written
        //   back to the server, additional blocks in the stash may be
        //   evicted into the path as long as the invariant is preserved
        //   and there is remaining space in the buckets.
        //   TODO
    {
        // Get leaf storing requested block (line 1)
        var x := posMap[addr];
        // Remap that block to new random leaf (line 2)
        posMap[addr] := RandomLeaf();
        
        // Get path from root to original leaf for requested block
        // (get value of P(x,l) in line 4 for all l in {0,...,L})
        var path := PathNodes(x);
        
        // Read all buckets in path into stash (lines 3-5)
        var l := 0;
        while l < |path|
            modifies this`stash
            invariant 0 <= l <= |path|
        {
            // Get blocks in each bucket
            var bucket := path[l];
            var blocks := tree.ReadBucket(bucket);
            var j := 0;
            while j < |blocks|
                modifies this`stash
            {
                // Add each block to stash
                var block := blocks[j];
                if block.addr >= 0 {  // Ignore dummy blocks
                    stash := stash[block.addr := block.data];
                }
                j := j + 1;
            }
            l := l + 1;
        }

        // TODO: need to prove this
        assume {:axiom} forall a :: a in stash.Keys ==> 0 <= a < N;
        
        // Read block (line 6)
        data := if addr in stash then Some(stash[addr]) else None;
        // Write block if requested (lines 7-9)
        if op == "W" {
            stash := stash[addr := newData.value];
        }

        // Get path from root to leaf for every block in stash
        // stashPaths[a'] is the path for the block with address a'
        // (i.e., stashPaths[a'] is the value of P(position[a'],l) in line 11
        //  for all a' in stash and all l in {0,...,L})
        var stashPaths: map<nat, seq<nat>> := map[];
        var remAddrs: set<nat> := stash.Keys;
        while |remAddrs| >= 0
            decreases remAddrs
            invariant |stashPaths| + |remAddrs| == |stash|
            invariant forall a :: a in stashPaths.Keys ==> a in stash.Keys
            invariant forall p :: p in stashPaths.Values ==> |p| == L+1
        {
            // Choose any remaining address in the stash
            var a :| a in remAddrs;
            remAddrs := remAddrs - {a};
            // Get leaf node storing that address
            var leaf := posMap[a];
            // Get path from root to that leaf
            var newPath := PathNodes(leaf);
            stashPaths := stashPaths[a := newPath];
        }
        assert |stash| == |stashPaths|;
        
        // Write back path (lines 10-15)
        l := |path| - 1;
        while l >= 0
        {
            // Line 11, but storing just the addresses a' (instead of (a',data'))
            var S' := set a' | a' in stash.Keys && path[l] == stashPaths[a'][l];
            // Select min(|S'|,Z) blocks from S' (line 12)
            var count := if |S'| < Z then |S'| else Z;
            var selectedBlocks: seq<Block> := [];
            var selectedAddrs: set<nat> := {};
            while count > 0
                invariant |selectedAddrs| + count <= |S'|
            {
                LemmaNonEmptySetDifference(S', selectedAddrs);
                var a :| a in S' - selectedAddrs;
                var newBlock := new Block(a, stash[a]);
                selectedBlocks := selectedBlocks + [newBlock];
                selectedAddrs := selectedAddrs + {a};
                count := count - 1;
            }
            // Remove selected blocks from stash (line 13)
            stash := stash - selectedAddrs;  // Dafny syntax is `map - (set of keys to remove)`
            // Add dummy blocks if necessary to get exactly Z blocks
            while |selectedBlocks| < Z
            {
                var newBlock := new Block(-1, "");
                selectedBlocks := selectedBlocks + [newBlock];
            }
            // Write selected blocks to tree (line 14)
            tree.WriteBucket(path[l], selectedBlocks);
            l := l - 1;
        }
    }

    // Whether the given node index represents a leaf node in the tree
    predicate IsLeaf(node: nat)
        reads this`treeSize
    {
        (treeSize-1)/2 <= node <= treeSize-1
    }

    // Correct length of path from root to given node
    function CorrectPathLength(node: nat) : nat
    {
        Math.FloorLog2(node+1) + 1
    }

    // TODO: prove this
    // Lemma: Path length for leaf nodes is tree height + 1
    lemma LemmaLeafCorrectPathLength(node: nat)
        ensures IsLeaf(node) ==> CorrectPathLength(node) == L + 1
    {
        assume {:axiom} IsLeaf(node) ==> CorrectPathLength(node) == L + 1;
    }

    // TODO: prove this
    // Lemma: If set S is larger than set T, then S - T is non-empty
    lemma LemmaNonEmptySetDifference(S: set, T: set)
        ensures |S| > |T| ==> exists x :: x in S - T
    {
        assume {:axiom} |S| > |T| ==> exists x :: x in S - T;
    }

    // TODO: update the below to conform with new code above

    // // Verifies the correctness property that a block is either in the stash or on its assigned path
    // predicate BlockInCorrectLocation(block: nat)
    //     requires block in posMap
    //     reads this`posMap, this`stash, this`tree
    // {
    //     var leaf := posMap[block];
    //     var path := PathNodes(leaf);
        
    //     // The block is either in the stash or on the path to its assigned leaf
    //     (block in stash) || 
    //     (exists node :: node in path && tree[node] == block)
    // }
    
    // // Verify all blocks follow Path ORAM invariants
    // method VerifyORAMInvariants() returns (valid: bool)
    //     ensures valid ==> forall b :: b in posMap ==> BlockInCorrectLocation(b)
    // {
    //     var allValid := true;
        
    //     // Check each block in the position map
    //     var blocks := posMap.Keys;
    //     foreach block in blocks
    //         invariant allValid ==> forall b :: b in blocks && b !in posMap ==> BlockInCorrectLocation(b);
    //     {
    //         if !BlockInCorrectLocation(block) {
    //             allValid := false;
    //             break;
    //         }
    //     }
        
    //     valid := allValid;
    //     return valid;
    // }
}
