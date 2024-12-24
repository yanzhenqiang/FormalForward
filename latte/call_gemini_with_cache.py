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
# response = model.generate_content('在latte的框架下，基于latte-list来实现Digits(用0-9来表示整数)')
response = model.generate_content('在latte的框架下，实现欧几里得公里体系，以及一个用这个体系中一个定理的证明')

print("\nToken Usage:")
print(response.usage_metadata)

print("\nResponse:")
print(response.text)