from fastapi import FastAPI, Request
from pydantic import BaseModel
import uvicorn
from wikipedia_path_oram import WikipediaPathORAM
from contextlib import asynccontextmanager
import sys


def create_app(articles_directory, pickle_file, database_file_name):
    # Lifespan-based initialization
    @asynccontextmanager
    async def lifespan(app: FastAPI):
        app.state.wikipedia_path_oram = WikipediaPathORAM(
            pickle_file=pickle_file
        ).load_articles(
            articles_directory=articles_directory,
            database_file_name=database_file_name,
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
    
    return app


def main():
    articles_directory, pickle_file, database_file_name = sys.argv[1:4]
    app = create_app(articles_directory, pickle_file, database_file_name)
    uvicorn.run(app, host="0.0.0.0", port=8080)


if __name__ == "__main__":
    main()
