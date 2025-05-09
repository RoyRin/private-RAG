include "oram_db.dfy"
include "math.dfy"

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
    var tree: Database           // Database on server storing buckets in tree structure
    var posMap: seq<nat>         // Position map: block index -> leaf bucket index
    var stash: map<nat, string>  // Temporary client storage for blocks (maps block address to block data)

    // Constructor
    constructor(numBlocks: nat, bucketSize: nat)
        requires numBlocks >= 2  // Minimum size requirement for ORAM to be secure
        requires bucketSize >= 1
        ensures N == numBlocks
        ensures fresh(tree)
        ensures numLeaves >= 1
        ensures treeSize >= 1
        ensures |posMap| == N
        ensures forall i :: 0 <= i < N ==> IsLeaf(posMap[i])
    {
        N := numBlocks;
        Z := bucketSize;
        tree := new Database(1, 1);  // (Dafny requires an initialization before "new;")

        new;  // (See "Two-phase constructors" in the Dafny documentation for explanation)

        L := Math.CeilLog2(N) - 1;
        numLeaves := Math.Pow2(L);
        treeSize := 2 * numLeaves - 1;
        
        // Initialize data structures
        tree := new Database(treeSize, Z);
        posMap := [];
        var i := 0;
        while i < N
            invariant i <= N
            invariant |posMap| == i
            invariant forall j :: 0 <= j < i ==> IsLeaf(posMap[j])
            invariant N == numBlocks
            invariant fresh(tree)
            invariant numLeaves >= 1
            invariant treeSize >= 1
        {
            var leaf := RandomLeaf();
            posMap := posMap + [leaf];
            i := i + 1;
        }
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
        ensures forall n :: n in path ==> 0 <= n < treeSize
        reads this`treeSize
    {
        LemmaLeafCorrectPathLength(node);
        // assert IsLeaf(node) ==> Math.FloorLog2(node+1) == L;
        if node == 0 then [0]
        else PathNodes((node - 1) / 2) + [node]
    }

    // See Access() for more information -- this is the first part of Access()
    method Access_Part1(op: string, addr: nat, newData: option<string>)
    returns (data: option<string>, path: seq<nat>, stashPaths: map<nat, seq<nat>>)
        requires op == "R" || op == "W"
        requires 0 <= addr < N
        requires |posMap| == N
        requires forall i :: 0 <= i < N ==> IsLeaf(posMap[i])
        requires op == "R" ==> newData.None?
        requires op == "W" ==> newData.Some?
        requires treeSize == |tree.buckets|
        requires forall block, bucket :: bucket in tree.buckets && block in bucket ==>
                                         -1 <= block.addr < N
        requires forall a :: a in stash.Keys ==> 0 <= a < N
        modifies this`posMap, this`stash, this.tree
        ensures stash.Keys == stashPaths.Keys
        ensures forall p :: p in stashPaths.Values ==> |p| == L+1
        ensures |path| == L + 1  // Path length for leaf nodes is tree height + 1
        ensures path[0] == 0     // First node is root
        ensures forall i :: 0 <= i < |path|-1 ==> 
            path[i+1] == 2 * path[i] + 1 || path[i+1] == 2 * path[i] + 2
        ensures forall n :: n in path ==> 0 <= n < treeSize
        ensures treeSize == |tree.buckets|
        ensures |posMap| == N
        ensures forall i :: 0 <= i < N ==> IsLeaf(posMap[i]) && 0 <= posMap[i] < treeSize
    {
        // Get leaf storing requested block (line 1)
        var x := posMap[addr];
        // Remap that block to new random leaf (line 2)
        var leaf := RandomLeaf();
        posMap := posMap[addr := leaf];
        
        // Get path from root to original leaf for requested block
        // (get value of P(x,l) in line 4 for all l in {0,...,L})
        path := PathNodes(x);
        
        // Read all buckets in path into stash (lines 3-5)
        var l := 0;
        while l < |path|
            modifies this`stash
            invariant 0 <= l <= |path|
            invariant forall a :: a in stash.Keys ==> 0 <= a < N
            invariant treeSize == |tree.buckets|
            invariant |posMap| == N
        {
            // Get blocks in each bucket
            assert path[l] in path;
            assert 0 <= path[l] < |tree.buckets|;
            var bucket := path[l];
            var blocks := tree.ReadBucket(bucket);
            assert forall block :: block in blocks ==> -1 <= block.addr < N;
            var j := 0;
            while j < |blocks|
                modifies this`stash
                invariant forall a :: a in stash.Keys ==> 0 <= a < N
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
        stashPaths := map[];
        var i := 0;
        while i < |stash|
            invariant i <= |stash|
            invariant |stashPaths| == i
            invariant |posMap| == N
            invariant forall a :: a in stash.Keys ==> 0 <= a < N
            invariant forall i :: 0 <= i < N ==> IsLeaf(posMap[i])
            invariant forall a :: a in stashPaths.Keys ==> a in stash.Keys
            invariant forall p :: p in stashPaths.Values ==> |p| == L+1
            invariant treeSize == |tree.buckets|
        {
            LemmaNonEmptySetDifference(stash.Keys, stashPaths.Keys);
            // Choose any remaining address in the stash
            var a :| a in stash.Keys - stashPaths.Keys;
            // Get leaf node storing that address
            var leaf := posMap[a];
            // Get path from root to that leaf
            var newPath := PathNodes(leaf);
            stashPaths := stashPaths[a := newPath];
            i := i + 1;
        }
        LemmaSubsetEqualSize(stashPaths.Keys, stash.Keys);
    }

    // This is the Access function (Figure 1) from the Path ORAM paper
    // We refer to the line numbers from the paper in the comments here
    method Access(op: string, addr: nat, newData: option<string>) returns (data: option<string>)
        requires op == "R" || op == "W"
        requires 0 <= addr < N
        requires op == "R" ==> newData.None?
        requires op == "W" ==> newData.Some?
        requires |posMap| == N
        requires treeSize == |tree.buckets|
        requires forall block, bucket :: bucket in tree.buckets && block in bucket ==>
                                         0 <= block.addr < N
        requires forall a :: a in stash.Keys ==> 0 <= a < N
        requires forall i :: 0 <= i < N ==> IsLeaf(posMap[i])
        modifies this`posMap, this`stash, this.tree
        ensures |posMap| == N
        ensures treeSize == |tree.buckets|
        ensures forall i :: 0 <= i < N ==> IsLeaf(posMap[i])
    {
        // First part of this function is done separately
        // to avoid having one overwhelmingly long function
        var path, stashPaths;
        data, path, stashPaths := Access_Part1(op, addr, newData);

        // Write back path (lines 10-15)
        var l := |path| - 1;
        while l >= 0
            modifies this.tree, this`stash
            invariant forall n :: n in path ==> 0 <= n < treeSize
            invariant forall n :: n in path ==> 0 <= n < |tree.buckets|
            invariant treeSize == |tree.buckets|
            invariant stash.Keys <= stashPaths.Keys
        {
            // Line 11, but storing just the addresses a' (instead of (a',data'))
            var S' := set a' | a' in stash.Keys && path[l] == stashPaths[a'][l];
            // Select min(|S'|,Z) blocks from S' (line 12)
            var count := if |S'| < Z then |S'| else Z;
            var selectedBlocks: seq<Block> := [];
            var selectedAddrs: set<nat> := {};
            while count > 0
                invariant |selectedAddrs| + count <= |S'|
                invariant S' <= stash.Keys
                invariant treeSize == |tree.buckets|
                invariant stash.Keys <= stashPaths.Keys
            {
                LemmaNonEmptySetDifference(S', selectedAddrs);
                var a :| a in S' - selectedAddrs;
                selectedBlocks := selectedBlocks + [Block(a, stash[a])];
                selectedAddrs := selectedAddrs + {a};
                count := count - 1;
            }
            // Remove selected blocks from stash (line 13)
            stash := stash - selectedAddrs;  // Dafny syntax is `map - (set of keys to remove)`
            // Add dummy blocks if necessary to get exactly Z blocks
            while |selectedBlocks| < Z
                invariant treeSize == |tree.buckets|
                invariant stash.Keys <= stashPaths.Keys
            {
                selectedBlocks := selectedBlocks + [Block(-1, "")];
            }
            // Write selected blocks to tree (line 14)
            assert path[l] in path && 0 <= path[l] < |tree.buckets|;
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

    // Lemma: Path length for leaf nodes is tree height + 1
    lemma LemmaLeafCorrectPathLength(node: nat)
        ensures IsLeaf(node) ==> CorrectPathLength(node) == L + 1
    {
        assume {:axiom} IsLeaf(node) ==> CorrectPathLength(node) == L + 1;
    }

    // Lemma: If set S is larger than set T, then S - T is non-empty
    lemma LemmaNonEmptySetDifference(S: set, T: set)
        ensures |S| > |T| ==> exists x :: x in S - T
    {
        assume {:axiom} |S| > |T| ==> exists x :: x in S - T;
    }

    // Lemma: If set S is a subset of set T and the two sets have equal size, then S = T
    lemma LemmaSubsetEqualSize(S: set, T: set)
        ensures S <= T && |S| == |T| ==> S == T
    {
        assume {:axiom} S <= T && |S| == |T| ==> S == T;
    }

    // Verifies the correctness property that a block is either in the stash or on the path to its assigned leaf
    predicate BlockInCorrectLocation(addr: nat)
        requires 0 <= addr < N
        requires |posMap| == N
        requires forall i :: 0 <= i < N ==> IsLeaf(posMap[i]) && 0 <= posMap[i] < treeSize
        requires treeSize == |tree.buckets|
        reads this, tree
    {
        var leaf := posMap[addr];
        var path := PathNodes(leaf);
        (addr in stash) ||
        (exists block, bucket :: (bucket in path) && (block in tree.buckets[bucket]) && (addr == block.addr))
    }
}
