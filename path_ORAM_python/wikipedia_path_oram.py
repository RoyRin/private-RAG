from path_oram import PathORAM
from pathlib import Path
import json
import pickle


class WikipediaPathORAM:
    def __init__(self, pickle_file: str):
        """
        Load past state from pickle, if pickle exists.
        Otherwise load_articles() must be called to create a fresh database.
        Calling save() writes the current state to the pickle.
        """
        self.pickle_file = pickle_file
        try:
            with open(self.pickle_file, 'rb') as f:
                self.__dict__.update(pickle.load(f).__dict__)
            print(f'Loaded Path ORAM from pickle: {pickle_file}.')
            self.loaded_from_pickle = True
        except FileNotFoundError:
            self.loaded_from_pickle = False

    def save(self):
        """Pickle this Wikipedia Path ORAM object for future use."""
        with open(self.pickle_file, 'wb') as f:
            pickle.dump(self, f)

    def load_articles(self, articles_directory: str, database_file_name: str, bucket_size: int, block_len: int):
        """
        - `articles_directory`: The directory holding the Wikipedia articles
        - `database_file_name`: The database file to hold the Path ORAM server
        - `bucket_size`: The number of blocks that each bucket holds
        - `block_len`: The size of each block in bytes

        Loads Wikipedia articles into a new Path ORAM database.
        `articles_directory` has to exist and contain Wikipedia articles.
        `database_file_name` need not exist and will be overwritten if it does.
        """

        # Do not load articles into fresh Path ORAM if using past state
        if self.loaded_from_pickle:
            return self

        def iter_articles():
            """Generator yielding all articles in `self.article_directory`."""
            for file_path in Path(articles_directory).rglob('*'):
                if not file_path.is_file() or file_path.name == '.DS_Store':
                    continue
                with open(file_path) as f:
                    articles = f.readlines()
                # Each article is a line from a file
                for article in articles:
                    article = article.strip()
                    yield article
        
        # Find total number of blocks needed to store all articles
        num_blocks = 0
        for article in iter_articles():
            num_blocks += -(len(article) // -block_len)  # Ceiling division

        # Path ORAM object
        self.path_oram = PathORAM(database_file_name, num_blocks, bucket_size, block_len)

        # Maps each Wikipedia article title to the list of the addresses
        # of all the blocks storing its contents, in order
        # (An article may be too large to fit in one block)
        self.title_to_addrs: dict[str, list[int]] = {}

        # Add all articles in directory to the database
        addr = 0  # Assign each block a unque address
        for article in iter_articles():
            title = json.loads(article)['title']
            print(f'Loading article into Path ORAM: {title}')
            self.title_to_addrs[title] = []
            # Place article contents into blocks
            for i in range(0, len(article), block_len):
                added_bytes = min(block_len, len(article)-i)
                padding_bytes = block_len - added_bytes
                # Create a block and record a unique address for it
                block_contents = article[i : i+added_bytes] + ' '*padding_bytes
                self.title_to_addrs[title].append(addr)
                # Write block to database
                self.path_oram.access('W', addr, block_contents)
                addr += 1
        
        self.path_oram.database.clear_access_log()
        self.save()
        print('Done.')

        return self

    def read(self, title: str) -> dict[str, str]:
        article = ''
        addrs = self.title_to_addrs[title]
        for addr in addrs:
            article += self.path_oram.access('R', addr)
        self.save()
        self.path_oram.database.write_access_log()
        self.path_oram.database.clear_access_log()
        return json.loads(article)
