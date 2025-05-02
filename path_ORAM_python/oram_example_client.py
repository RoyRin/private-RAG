import requests

query = "Biology"

response = requests.post("http://localhost:8080/rag",
                         json={"encrypted_query": query})

print(response)
for i, result in enumerate(response.json()["results"]):
    print(f"{i+1}. {result}\n")
