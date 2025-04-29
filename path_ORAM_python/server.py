import sqlite3
import json
from typing import List, Tuple


# A block, which consists of an address and some data
# addr = -1 represents dummy block
class Block:
    def __init__(self, addr: int, data: str):
        self.addr: int = addr
        self.data: str = data


# The database held in the server
class Database:
    def __init__(self, file_name: str, initial_db: list[tuple[int, str]]):
        self.file_name = file_name
        self.access_log: List[Tuple[str, int]] = []
        conn = sqlite3.connect(self.file_name)
        cursor = conn.cursor()
        cursor.execute('DROP TABLE IF EXISTS db')
        cursor.execute('CREATE TABLE db (key INTEGER PRIMARY KEY, value TEXT)')
        cursor.executemany('INSERT INTO db (key, value) VALUES (?, ?)', initial_db)
        conn.commit()
        conn.close()

    def read_bucket(self, bucket: int) -> List[Block]:
        self.access_log.append(('R', bucket))
        conn = sqlite3.connect(self.file_name)
        cursor = conn.cursor()
        cursor.execute('SELECT value FROM db WHERE key = ?', (bucket,))
        blocks_serialized = cursor.fetchone()[0]
        blocks = [Block(int(block[0]), block[1]) for block in json.loads(blocks_serialized)]
        conn.commit()
        conn.close()
        return blocks

    def write_bucket(self, bucket: int, blocks: List[Block]):
        self.access_log.append(('W', bucket))
        blocks_serialized = json.dumps([[block.addr, block.data] for block in blocks])
        conn = sqlite3.connect(self.file_name)
        cursor = conn.cursor()
        cursor.execute('INSERT OR REPLACE INTO db (key, value) VALUES (?, ?)', (bucket, blocks_serialized))
        conn.commit()
        conn.close()

    def write_access_log(self):
        print(self.access_log)

    def clear_access_log(self):
        self.access_log.clear()
