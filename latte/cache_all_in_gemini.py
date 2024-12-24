import os
import google.generativeai as genai
from google.generativeai import caching
import datetime
import time
import subprocess

def get_files_from_command():
    command = 'find ./ -type f | grep "cljc$\|clj$" | grep "/src/" | grep -v "\-kernel"'
    try:
        result = subprocess.run(command, shell=True, capture_output=True, text=True)
        if result.returncode == 0:
            return [line.strip() for line in result.stdout.splitlines()]
        return []
    except subprocess.SubProcessError as e:
        print(f"Error executing command: {e}")
        return []

def read_file_content(file_path):
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return f"--- File: {file_path} ---\n{f.read()}\n\n"
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return ""

def merge_files(file_paths):
    merged_content = ""
    total_size = 0
    
    for file_path in file_paths:
        content = read_file_content(file_path)
        content_size = len(content.encode('utf-8'))        
        if total_size + content_size > 2 * 1024 * 1024:
            print(f"Warning: Reached size limit. Stopping at {file_path}")
            break
            
        merged_content += content
        total_size += content_size
        
    return merged_content

def create_temp_file(content):
    temp_file = "temp_merged_code.txt"
    with open(temp_file, "w", encoding="utf-8") as f:
        f.write(content)
    return temp_file

def main():
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key:
        print("Please set GEMINI_API_KEY environment variable")
        return
    
    genai.configure(api_key=api_key)
    
    file_paths = get_files_from_command()
    if not file_paths:
        print("No matching files found")
        return
    
    print(f"Found {len(file_paths)} matching files")
    merged_content = merge_files(file_paths)
    
    temp_file = create_temp_file(merged_content)
    
    try:
        code_file = genai.upload_file(path=temp_file)        
        while code_file.state.name == 'PROCESSING':
            print('Waiting for file to be processed...')
            time.sleep(2)
            code_file = genai.get_file(code_file.name)
        
        print(f'File processing complete: {code_file.uri}')
        
        # Create a cache with a 30 minute TTL
        cache = caching.CachedContent.create(
            model='models/gemini-1.5-flash-001',
            display_name='clojure_codebase',
            system_instruction=(
                'You are an expert code analyzer. Your task is to analyze '
                'this Clojure codebase and answer questions about its structure, '
                'functionality, and implementation details.'
            ),
            contents=[code_file],
            ttl=datetime.timedelta(minutes=30),
        )
        
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
        
        print("\nCache information saved to cache_info.txt")
        
    finally:
        if os.path.exists(temp_file):
            os.remove(temp_file)


if __name__ == "__main__":
    main()