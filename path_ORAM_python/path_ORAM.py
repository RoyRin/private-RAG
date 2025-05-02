from server import Block, Database
import math
import random
import json
from typing import Dict, List, Literal


class PathORAM:
    MIN_BLOCKS = 2

    def __init__(self, database_file_name: str, num_blocks: int, bucket_size: int, block_len: int):
        assert num_blocks >= self.MIN_BLOCKS
        assert bucket_size >= 1

        # Name of file holding the database
        self.database_file_name = database_file_name
        # Total number of blocks
        self.N = num_blocks
        # Bucket size (i.e., how many blocks in each tree node)
        self.Z = bucket_size
        # Block size (i.e., how many bytes in each block's contents)
        self.block_len = block_len
        # Height of the tree
        self.L = math.ceil(math.log2(self.N))
        # Number of leaves
        self.num_leaves = 2 ** self.L 
        # Total size of the tree
        self.tree_size = 2 * self.num_leaves - 1

        # Database on server storing buckets in tree structure
        # Initialized such that each bucket is filled with dummy blocks,
        # and bucket indices go from 0 to tree_size-1
        dummy_blocks_serialized = json.dumps([[-1, ' '*self.block_len] for _ in range(self.Z)])
        empty_db = [(i, dummy_blocks_serialized) for i in range(self.tree_size)]
        self.database = Database(self.database_file_name, empty_db)

        # Position map: block address -> leaf bucket index
        self.pos_map: List[int] = [self.random_leaf() for _ in range(self.N)]
        # Temporary client storage for blocks (maps block address to block data)
        self.stash: Dict[int, str] = {}

        random.seed(0)

    # Select the index of a leaf node uniformly at random
    def random_leaf(self) -> int:
        return random.randint((self.tree_size - 1) // 2, self.tree_size - 1)

    # Returns sequence of indices of the nodes from the root to the input node
    # When called on a leaf x, gives the value of P(x,l) from the paper for each l in {0,...,L}
    def path_nodes(self, node: int) -> List[int]:
        path = []
        while node != 0:
            path.append(node)
            node = (node - 1) // 2
        path.append(0)
        return list(reversed(path))

    # This is the Access function (Figure 1) from the Path ORAM paper
    # We refer to the line numbers from the paper in the comments here
    def access(self, op: Literal['R', 'W'], addr: int, new_data: str | None = None) -> str | None:
        assert op == 'R' or op == 'W'
        assert 0 <= addr and addr < self.N
        if op == 'R':
            assert new_data is None
        if op == 'W':
            assert isinstance(new_data, str)

        # Get leaf storing requested block (line 1)
        x = self.pos_map[addr]
        # Remap that block to new random leaf (line 2)
        self.pos_map[addr] = self.random_leaf()

        # Get path from root to original leaf for requested block
        # (get value of P(x,l) in line 4 for all l in {0,...,L})
        path = self.path_nodes(x)

        # Read all buckets in path into stash (lines 3-5)
        for bucket in path:
            blocks = self.database.read_bucket(bucket)
            for block in blocks:
                if block.addr >= 0:  # Ignore dummy blocks
                    self.stash[block.addr] = block.data

        # Read block (line 6)
        data = self.stash[addr] if addr in self.stash else None
        # Write block if requested (lines 7-9)
        if op == 'W':
            self.stash[addr] = new_data

        # Get path from root to leaf for every block in stash
        # stashPaths[a'] is the path for the block with address a'
        # (i.e., stashPaths[a'] is the value of P(position[a'],l) in line 11
        #  for all a' in stash and all l in {0,...,L})
        stash_paths: Dict[int, List[int]] = {}
        for a in self.stash.keys():
            leaf = self.pos_map[a]
            stash_paths[a] = self.path_nodes(leaf)

        # Write back path (lines 10-15)
        for l in reversed(range(len(path))):
            # Select min(|S'|,Z) blocks from the set S' as defined in Figure 1
            # and remove them from the stash (lines 11-13)
            selected_blocks: List[Block] = []
            for a, d in self.stash.copy().items():
                if path[l] == stash_paths[a][l]:  # Condition for being in S'
                    selected_blocks.append(Block(a, d))
                    del self.stash[a]
                    if len(selected_blocks) == self.Z:  # Limit to Z blocks
                        break
            # Add dummy blocks if necessary to get exactly Z blocks
            while len(selected_blocks) < self.Z:
                selected_blocks.append(Block(-1, ' '*self.block_len))
            # Write selected blocks to tree (line 14)
            self.database.write_bucket(path[l], selected_blocks)

        return data
