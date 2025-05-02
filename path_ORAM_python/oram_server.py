from fastapi import FastAPI, Request
from pydantic import BaseModel
from typing import Optional
import uvicorn
import base64
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
import os
from pathlib import Path
import sys
import uvicorn


app = FastAPI()


# 🧾 Request schema
class Query(BaseModel):
    encrypted_query: str


@app.post("/oram_read")
async def rag_endpoint(query: Query):
    # TODO  - MAKE some business logic to handle query (even if query is not there)
    user_query = query.encrypted_query  # use plaintext

    response = None # DENNIS DO ORAM READ


    return {"results": [response]}


@app.post("/test")
async def rag_endpoint(query: Query):
    print(f"query {query}")
    return {"results": ["hi"]}



def main():
    # DENNIS - DO ORAM SET UP

    uvicorn.run("oram_server:app", host="0.0.0.0", port=8080)


if __name__ == "__main__":
    print("hello!")
    main()
