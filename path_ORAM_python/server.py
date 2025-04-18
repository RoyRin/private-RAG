from typing import List, Tuple


# A block, which consists of an address and some data
# addr = -1 represents dummy block
class Block:
    def __init__(self, addr: int, data: str):
        self.addr: int = addr
        self.data: str = data


# A bucket containing bucket_size blocks
class Bucket:
    def __init__(self, bucket_size: int):
        self.blocks: List[Block] = [Block(-1, "") for _ in range(bucket_size)]


# The database held in the server,
# composed of database_size buckets, each of which holds bucket_size blocks
class Database:
    def __init__(self, database_size: int, bucket_size: int):
        self.database_size = database_size
        self.bucket_size = bucket_size
        self.buckets: List[Bucket] = [Bucket(bucket_size) for _ in range(database_size)]
        self.access_log: List[Tuple[str, int]] = []

    def read_bucket(self, bucket: int) -> List[Block]:
        self.access_log.append(('R', bucket))
        return self.buckets[bucket].blocks

    def write_bucket(self, bucket: int, blocks: List[Block]):
        self.access_log.append(('W', bucket))
        self.buckets[bucket].blocks = blocks

    def write_access_log(self):
        print(self.access_log)

    def clear_access_log(self):
        self.access_log.clear()
