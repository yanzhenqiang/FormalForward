import os
import google.generativeai as genai
from google.generativeai import caching
import datetime
import time
import subprocess

for c in caching.CachedContent.list():
  print(c)
cache = caching.CachedContent.get("cachedContents/9lk72s3w69bh")

model = genai.GenerativeModel.from_cached_content(cached_content=cache)        
response = model.generate_content('Give me a high-level overview of this codebase.')
print("\nToken Usage:")
print(response.usage_metadata)

print("\nResponse:")
print(response.text)

# Save cache info for future reference
with open("cache_info.txt", "w") as f:
    f.write(f"Cache URI: {cache.name}\n")
    f.write(f"Display Name: {cache.display_name}\n")
    f.write(f"Creation Time: {cache.create_time}\n")
    f.write(f"Expiration Time: {cache.expire_time}\n")