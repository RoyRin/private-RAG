import math
import numpy as np
import random
from typing import List, Dict, Union, Optional, TextIO

class PathORAM:
    def __init__(self, num_blocks: int, initial_data: Optional[Dict[int, int]] = None):
        """Initialize Path ORAM with given number of blocks and optional initial data.
        
        Args:
            num_blocks: Total number of blocks in the ORAM
            initial_data: Optional dictionary mapping block IDs to their initial values
        """
        self.N = num_blocks
        self.L = int(math.ceil(math.log(self.N, 2)) - 1)  # height of the tree
        self.num_leafs = int(math.pow(2, self.L) - 1)
        self.tree_size = int(math.pow(2, self.L + 1) - 1)
        
        # Initialize tree structure
        self.tree = [0] * self.tree_size
        for i in range(1, self.N + 1):
            self.tree[i] = i
        random.shuffle(self.tree)
        
        # Initialize position map
        self.pos_map = {x: random.randint(0, self.num_leafs - 1) 
                       for x in range(1, self.N + 1)}
        
        # Update position map based on initial tree state
        for i in range(self.tree_size):
            block = self.tree[i]
            if block != 0:
                self.pos_map[block] = self._random_path(i)
        
        # Initialize stash and data
        self.stash: List[int] = []
        self.stash_data: Dict[int, int] = {}
        self.data = initial_data or {}
        
        # Initialize data with random values if not provided
        if not initial_data:
            for i in self.tree:
                self.data[i] = random.randint(1000, 10000)
        
        # Operation buffers
        self.buffer_r: List[List[str]] = []
        self.buffer_w: List[List[str]] = []
    
    def _read_leaf(self, branch: int) -> int:
        """Convert branch number to leaf node index."""
        return int(int(math.pow(2, self.L)) + int(branch) - 1)
    
    def _get_parent(self, node: int) -> int:
        """Get parent node index."""
        return int(math.floor((node - 1) / 2.0))
    
    def _path_nodes(self, branch: int) -> List[int]:
        """Get list of nodes in path from root to leaf."""
        path = []
        for _ in range(0, self.L + 1):
            path.append(branch)
            branch = self._get_parent(branch)
        return list(reversed(path))
    
    def _random_path(self, node: int) -> int:
        """Generate random path from node to leaf."""
        rand = random.randint(0, 1)
        child1 = 2 * node + 1
        child2 = 2 * node + 2
        
        if child2 > (self.tree_size - 1):
            return int(node - self.num_leafs)
        else:
            return self._random_path(child1) if rand == 0 else self._random_path(child2)
    
    def _read_bucket(self, block: int) -> int:
        """Read data from a bucket."""
        self.buffer_r.append(['R', block])
        return self.data[block]
    
    def _write_bucket(self, block: int, new_data: int) -> None:
        """Write data to a bucket."""
        self.buffer_w.append(['W', block])
        self.data[block] = new_data
    
    def access(self, op: str, block: int, new_data: Optional[int] = None) -> None:
        """Access (read/write) a block in the ORAM.
        
        Args:
            op: Operation type ('R' for read, 'W' for write)
            block: Block ID to access
            new_data: New data to write (only for write operations)
        """
        # Get and update position
        x = self.pos_map.get(block)
        self.pos_map[block] = np.random.randint(0, self.num_leafs - 1)
        
        # Read path
        leaf_node = self._read_leaf(x)
        path = self._path_nodes(leaf_node)
        for node in path:
            blocks = self.tree[node]
            self.stash.append(blocks)
            self.stash_data[blocks] = self._read_bucket(blocks)
        
        # Write operation
        if op == 'W':
            self.stash_data[block] = new_data
        
        # Write back path
        for node in reversed(path):
            n = self.tree[node]
            self._write_bucket(n, self.stash_data.get(n))
            for i in self.stash[:]:  # Create a copy to iterate
                if i == 0:
                    self.stash.remove(i)
                    self.stash_data.pop(i, None)
                else:
                    current_branch = self.pos_map.get(i)
                    a = self._path_nodes(current_branch)
                    if node in a:
                        self.tree[node] = i
                        self.stash.remove(i)
                        self.stash_data.pop(i, None)
    
    def write_access_log(self, output_file: TextIO) -> None:
        """Write access log to output file.
        
        Args:
            output_file: File object to write to
        """
        buffer = self.buffer_r + list(reversed(self.buffer_w))
        for i in buffer:
            output_file.write(f"{i[0]} {i[1]}\n")
    
    def clear_buffers(self) -> None:
        """Clear operation buffers."""
        self.buffer_r.clear()
        self.buffer_w.clear()

# Example usage:
def process_oram_operations(in_file_path: str, out_file_path: str) -> Dict:
    # Read input file
    with open(in_file_path, 'r') as f:
        N = int(f.readline().strip())
        operations = [line.strip().split() for line in f.readlines()]
    
    # Initialize ORAM
    oram = PathORAM(N)
    unit_test = {}
    
    # Process operations
    with open(out_file_path, 'w') as out_file:
        for op, block in operations:
            block = int(block)
            if op == 'R':
                oram.access(op, block)
            else:  # op == 'W'
                oram.access(op, block, random.randint(1000, 5000))
            
            oram.write_access_log(out_file)
            unit_test[str(block)] = oram.buffer_r.copy()
            oram.clear_buffers()
    
    return unit_test

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 3:
        print("Usage: python path_ORAM.py <input_file> <output_file>")
        sys.exit(1)
    
    unit_test = process_oram_operations(sys.argv[1], sys.argv[2])
    print(unit_test)