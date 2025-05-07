# private-RAG

This repository contains our formal verification of Path ORAM in Dafny and our implementation of a Wikipedia RAG that keeps article access patterns secure by accessing them through Path ORAM.


## Quick Start

### The server

To start the server, run
```
python path_ORAM_python/oram_server.py example_wiki path_ORAM_python/wikipedia_path_oram.pkl path_ORAM_python/wikipedia_path_oram.db
```

The first time you run this, this creates a pickle file (`path_ORAM_python/wikipedia_path_oram.pkl`) to persist information needed by the Path ORAM object for subsequent runs (including the stash and other metadata), as well as a database file (`path_ORAM_python/wikipedia_path_oram.db`) to hold the main Path ORAM database. (This database is the untrusted storage from which the Path ORAM object hides the access patterns.) Then all the Wikipedia articles in `example_wiki` are loaded into the Path ORAM structure, which can take 3-4 minutes to complete.

As long as you keep the pickle and database files around, in subsequent runs, the server will pick up where it left off by loading its previous state from the pickle. This avoids the delay that comes from having to load the articles into Path ORAM. (Of course, you can do a reset by deleting the pickle and database, and the server will load the articles from scratch.)

### The client

While the server is running, make queries with the client using the following command (replacing "Fenway Park" with the article title you'd like to query):
```
python path_ORAM_python/oram_example_client.py "Fenway Park"
```

In a complete RAG system, the user's query should be able to be arbitrary, with the RAG server identifying the relevant articles given the query. In this simplified system, where the goal is to demonstrate Path ORAM, you will have to supply an exact article title, and the result will be the contents of the article. Also `example_wiki` contains only a tiny fraction of Wikipedia, and you can only query article titles from this data. A lot of the article titles are redirect pages with no content. Some other article titles that do return interesting results include: "A", "Academy Awards", "Anarchism", "FIFA", "Foobar", "Friction".

Articles are accessed through the Path ORAM system. When you make queries with the client, you can look in the terminal in which the server is running to see the database access patterns. This is outputted in a list of pairs of the form `('R', 2540)` or `('W', 2540)` (representing a read or write of index 2540 in the database).


## File Structure

<pre>
<b>example_wiki</b> - Some Wikipedia articles

<b>path_ORAM_dafny</b> - Formal verification of Path ORAM
├── <b>math.dfy</b> - Some mathematical functions
├── <b>oram_db.dfy</b> - Represents the untrusted server storage in Path ORAM
└── <b>path_oram.dfy</b> - Verified implementation of Path ORAM

<b>path_ORAM_python</b> - Implementation of Path ORAM for Wikipedia RAG
├── <b>oram_db.py</b> - Untrusted server storage in Path ORAM; accesses the SQL database
├── <b>oram_example_client.py</b> - Client for making queries to access Wikipedia articles through Path ORAM
├── <b>oram_server.py</b> - Server for handling client queries and returning Wikipedia articles
├── <b>path_oram.py</b> - Implementation of Path ORAM object
└── <b>wikipedia_path_oram.py</b> - Wrapper around Path ORAM object for handling Wikipedia articles
</pre>
