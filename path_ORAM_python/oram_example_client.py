import requests

query = "Fenway Park"

response = requests.post("http://localhost:8080/read",
                         json={"encrypted_query": query})

print(response)
print(response.json()["results"])
