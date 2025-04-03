include "math.dfy"

class PathORAM {
    // Core ORAM parameters
    var N: nat        // Total number of blocks
    var L: nat        // Height of the tree
    var numLeafs: nat // Number of leaf nodes
    var treeSize: nat // Total size of the tree
    
    // Data structures
    var tree: array<nat>        // Tree structure mapping nodes to blocks
    var posMap: map<nat, nat>   // Position map: block -> leaf
    var stash: seq<nat>         // Temporary storage for blocks
    var stashData: map<nat, nat>// Block data in stash
    var data: map<nat, nat>     // Main data storage
    
    // Access pattern buffers
    var bufferR: seq<(string, nat)> // Read operations log
    var bufferW: seq<(string, nat)> // Write operations log

    // Constructor
    constructor(numBlocks: nat)
        requires numBlocks >= Math.MIN_BLOCKS  // At least 2 blocks required
        ensures N == numBlocks
        ensures fresh(tree)
        ensures L >= 1  // Tree has at least one level
        ensures numLeafs > 0
        ensures treeSize > 0
        ensures forall i :: 0 <= i < treeSize ==> tree[i] == 0  // Tree initialized empty
    {
        N := numBlocks;
        var logN := Math.CeilLog2(N);
        L := logN - 1;  // Safe since CeilLog2(N) >= 2
        
        // Calculate tree parameters
        var powL := Math.Pow2(L);
        Math.Pow2Positive(L);
        numLeafs := powL - 1;
        
        var powL1 := Math.Pow2(L + 1);
        Math.Pow2Increases(L + 1, L);
        treeSize := powL1 - 1;
        
        // Verify tree size properties
        Math.Pow2Positive(L);
        Math.Pow2Increases(L + 1, L);
        
        // Initialize data structures
        tree := new array<nat>(treeSize);
        posMap := map[];
        stash := [];
        stashData := map[];
        data := map[];
        bufferR := [];
        bufferW := [];
        
        // Initialize tree with zeros
        var i := 0;
        while i < treeSize
            modifies tree
            invariant 0 <= i <= treeSize
            invariant forall k :: 0 <= k < i ==> tree[k] == 0
        {
            tree[i] := 0;
            i := i + 1;
        }
    }

    method {:private} ReadLeaf(branch: nat) returns (leaf: nat)
        requires branch >= 0
        requires branch < numLeafs
        ensures leaf == Math.Pow2(L) + branch - 1
    {
        leaf := Math.Pow2(L) + branch - 1;
    }

    method {:private} GetParent(node: nat) returns (parent: nat)
        requires node > 0
        requires node < treeSize
        ensures parent == (node - 1) / 2
    {
        parent := (node - 1) / 2;
    }

    method {:private} PathNodes(branch: nat) returns (path: seq<nat>)
        requires branch >= 0
        requires branch < treeSize
        ensures |path| == L + 1  // Path length is tree height + 1
        ensures path[0] == 0     // First node is root
        ensures forall i :: 0 <= i < |path|-1 ==> 
            path[i+1] == 2 * path[i] + 1 || path[i+1] == 2 * path[i] + 2
    {
        var curr := branch;
        var temp: seq<nat> := [];
        
        // Build path from leaf to root
        while curr >= 0
            invariant curr >= 0
            invariant |temp| <= L + 1
            decreases curr
        {
            temp := temp + [curr];
            if curr == 0 { break; }
            var parent := (curr - 1) / 2;
            curr := parent;
        }
        
        // Reverse path to get root-to-leaf order
        path := [];
        var i := |temp| - 1;
        while i >= 0
            invariant -1 <= i < |temp|
            invariant |path| == |temp| - (i + 1)
            decreases i
        {
            path := path + [temp[i]];
            i := i - 1;
        }
    }

    method {:private} RandomPath(node: nat) returns (path: nat)
        requires node >= 0
        requires node < treeSize
        ensures 0 <= path < numLeafs
    {
        // In real implementation, this would use a cryptographically secure RNG
        var rand := if node % 2 == 0 then 0 else 1;
        var child1 := 2 * node + 1;
        var child2 := 2 * node + 2;
        
        if child2 >= treeSize {
            path := node - numLeafs;
        } else {
            if rand == 0 {
                path := RandomPath(child1);
            } else {
                path := RandomPath(child2);
            }
        }
    }

    method {:private} ReadBucket(block: nat) returns (value: nat)
        requires block >= 0
        requires block in data
        modifies this`bufferR
        ensures value == data[block]
        ensures bufferR == old(bufferR) + [('R', block)]
    {
        // Log the read operation
        bufferR := bufferR + [('R', block)];
        value := data[block];
    }

    method {:private} WriteBucket(block: nat, newData: nat)
        requires block >= 0
        modifies this`data, this`bufferW
        ensures data == old(data)[block := newData]
        ensures bufferW == old(bufferW) + [('W', block)]
    {
        // Log the write operation and update data
        bufferW := bufferW + [('W', block)];
        data := data[block := newData];
    }

    method Access(op: string, block: nat, newData: nat?)
        requires op == "R" || op == "W"
        requires block >= 0 && block < N
        requires op == "W" ==> newData != null
        modifies this`data, this`posMap, this`stash, this`stashData,
                 this`bufferR, this`bufferW, this`tree
        ensures op == "W" ==> block in data && data[block] == newData
        // ORAM correctness invariants
        ensures block in posMap
        ensures posMap[block] != old(posMap[block])
        // The block is either in a bucket along the path to the leaf, or in the stash
        ensures (exists i :: 0 <= i < |stash| && stash[i] == block) || 
                (exists node :: 0 <= node < treeSize && tree[node] == block)
    {
        // Get current position and update to new random position
        var oldPos := if block in posMap then posMap[block] else 0;
        var newPos := RandomPath(0);
        posMap := posMap[block := newPos];
        
        // Read path
        var leafNode := ReadLeaf(oldPos);
        var path := PathNodes(leafNode);
        
        // Read all blocks in path into stash
        var i := 0;
        while i < |path|
            modifies this`stash, this`stashData, this`bufferR
            invariant 0 <= i <= |path|
        {
            var node := path[i];
            var blockInNode := tree[node];
            if blockInNode != 0 {
                stash := stash + [blockInNode];
                var blockData := ReadBucket(blockInNode);
                stashData := stashData[blockInNode := blockData];
            }
            i := i + 1;
        }
        
        // Perform write if needed
        if op == "W" {
            stashData := stashData[block := newData.value];
        }
        
        // Write back path
        var pathLen := |path|;
        if pathLen > 0 {
            i := pathLen - 1;
        } else {
            i := 0;
        }
        while i >= 0
            modifies this`tree, this`stash, this`stashData, this`bufferW
            invariant -1 <= i < |path|
        {
            var node := path[i];
            var blockInNode := tree[node];
            
            if blockInNode != 0 && blockInNode in stashData {
                WriteBucket(blockInNode, stashData[blockInNode]);
            }
            
            // Try to push blocks from stash back into tree
            var j := 0;
            while j < |stash|
                modifies this`tree, this`stash, this`stashData
                invariant 0 <= j <= |stash|
            {
                var stashBlock := stash[j];
                if stashBlock != 0 {
                    var stashBlockPath := if stashBlock in posMap then posMap[stashBlock] else 0;
                    var stashBlockNodes := PathNodes(stashBlockPath);
                    
                    if node in stashBlockNodes {
                        tree[node] := stashBlock;
                        stash := stash[..j] + stash[j+1..];
                        stashData := map b | b in stashData && b != stashBlock :: stashData[b];
                        j := j - 1;  // Adjust for removed element
                    }
                }
                j := j + 1;
            }
            i := i - 1;
        }
    }

    // Verifies the correctness property that a block is either in the stash or on its assigned path
    predicate BlockInCorrectLocation(block: nat)
        requires block in posMap
        reads this`posMap, this`stash, this`tree
    {
        var leaf := posMap[block];
        var path := PathNodes(leaf);
        
        // The block is either in the stash or on the path to its assigned leaf
        (block in stash) || 
        (exists node :: node in path && tree[node] == block)
    }
    
    // Verify all blocks follow Path ORAM invariants
    method VerifyORAMInvariants() returns (valid: bool)
        ensures valid ==> forall b :: b in posMap ==> BlockInCorrectLocation(b)
    {
        var allValid := true;
        
        // Check each block in the position map
        var blocks := posMap.Keys;
        foreach block in blocks
            invariant allValid ==> forall b :: b in blocks && b !in posMap ==> BlockInCorrectLocation(b);
        {
            if !BlockInCorrectLocation(block) {
                allValid := false;
                break;
            }
        }
        
        valid := allValid;
        return valid;
    }

    method WriteAccessLog()
        requires |bufferR| >= 0 && |bufferW| >= 0
        ensures |bufferR| == 0 && |bufferW| == 0
    {
        // In a real implementation, this would write to a file
        // For verification purposes, we just clear the buffers
        ClearBuffers();
    }

    method ClearBuffers()
        modifies this`bufferR, this`bufferW
        ensures |bufferR| == 0
        ensures |bufferW| == 0
    {
        bufferR := [];
        bufferW := [];
    }
}
