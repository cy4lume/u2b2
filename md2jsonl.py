import json
import re


new_md_path = "php-5.md"

# New parser for Setext-style heading markdown (used in PHP manual)
new_sections = []
heading = None
buffer = []

with open(new_md_path, 'r', encoding='utf-8') as f:
    lines = f.readlines()

i = 0
while i < len(lines) - 1:
    line = lines[i].strip()
    next_line = lines[i + 1].strip()

    # Check for Setext-style headings (=== or ---)
    if re.match(r'^=+$', next_line) or re.match(r'^-+$', next_line):
        # Save previous section
        if heading and buffer:
            new_sections.append((heading, '\n'.join(buffer).strip()))
        heading = line
        buffer = []
        i += 2  # skip heading underline
    else:
        buffer.append(line)
        i += 1

# Add last section
if heading and buffer:
    new_sections.append((heading, '\n'.join(buffer).strip()))

# Write to JSONL
new_jsonl_path = 'php_manual_deepseek.jsonl'
with open(new_jsonl_path, 'w', encoding='utf-8') as out_f:
    for heading, content in new_sections:
        if not content.strip():
            continue
        record = {
            "instruction": heading,
            "input": "",
            "output": content.strip()
        }
        out_f.write(json.dumps(record, ensure_ascii=False) + '\n')

len(new_sections), new_jsonl_path
