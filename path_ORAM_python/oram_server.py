from fastapi import FastAPI, Request
from pydantic import BaseModel
import uvicorn
from wikipedia_path_oram import WikipediaPathORAM
from contextlib import asynccontextmanager


# Lifespan-based initialization
@asynccontextmanager
async def lifespan(app: FastAPI):
    app.state.wikipedia_path_oram = WikipediaPathORAM(
        pickle_file='C:/Users/denni/OneDrive/Desktop/Courses/CS 2540/Final Project/private-RAG/path_ORAM_python/wikipedia_path_oram.pkl'
    ).load_articles(
        articles_directory='C:/Users/denni/OneDrive/Desktop/Courses/CS 2540/Final Project/example_wiki',
        database_file_name='C:/Users/denni/OneDrive/Desktop/Courses/CS 2540/Final Project/private-RAG/path_ORAM_python/wikipedia_path_oram.db',
        bucket_size=4,
        block_len=4096
    )
    yield


# Create app with lifespan
app = FastAPI(lifespan=lifespan)


# Request schema
class Query(BaseModel):
    encrypted_query: str


@app.post("/read")
async def rag_endpoint(query: Query, request: Request):
    user_query = query.encrypted_query  # use plaintext
    try:
        response = request.app.state.wikipedia_path_oram.read(user_query)
    except KeyError as key_error:
        response = {"key_error": str(key_error)}
    return {"results": response}


def main():
    uvicorn.run("oram_server:app", host="0.0.0.0", port=8080)


if __name__ == "__main__":
    main()
