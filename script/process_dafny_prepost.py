# This file contains a script for assessing the capabilities of LLMs to
# generate pre and post conditions for programs in Dafny.  
# The script processes a set of Dafny files, removing the pre/post conditions,
# and then uses an LLM to generate new pre/post conditions for the files.
# The script then verifies the generated files using the Dafny verifier.
# The script outputs a CSV file with the results of the verification process.
# The script also outputs a log file with the results of the processing.

####### Initial definitions #######

# Enumeration of supported APIs
class API:
    OpenAI = 1
    Antrophic = 2
    DeepSeek = 3

# Data structure with API, model, temperature (0=default), and maximum attempts
class LLMData:
    def __init__(self, api, model, temperature, attempts, max_failures):
        self.api = api
        self.model = model
        self.temperature = temperature
        self.attempts = attempts
        self.max_failures = max_failures

####### Configuration parameters #######

# Folder with source files in Dafny (with extension .dfy)
input_folder = r"..."

# Folder to place generated files in Dafny (different from the previous folder)
output_folder_base = r"..."

# OpenAI API key
openai_key = r"..."

# Antrophic API key
antrophic_key = r"..."

# Path to the Dafny executable 
dafny_executable = r"..."

# Verbosity level (0: no output, 1: some output, 2: detailed output)
verbose = 1

# verifier timeout in seconds
verifier_timeout = 60

# List of LLMs to try in sequence
# llms = [LLMData(API.DeepSeek, "deepseek-chat", 0.5, 5, 5)]˜
llms = [LLMData(API.OpenAI, "gpt-4o-2024-08-06", 0.5, 5, 5)]
# llms = [LLMData(API.Antrophic, "claude-3-5-sonnet-20241022", 0.5, 5, 5)]    
        
#####  Imports ##### 
import os
import subprocess
from openai import OpenAI
import traceback
import time
import anthropic


#####  Prompts #####

minimal_prompt = """Add adequate pre and post conditions (requires/ensures clauses) in the following Dafny code, taking into account the following instructions:
- The original Dafny code is provided between BEGIN DAFNY and END DAFNY.
- Do not modify the original code, just add the needed requires and ensures clauses!
- Do just output the Dafny code, without explanations."""

base_prompt_fix = """You are an expert in the Dafny programming language and formal verification. 
Your task is to fix the pre and post conditions in the following Dafny code, which does not currently pass the Dafny verifier.
Take into account the following:
- The original Dafny code is provided between BEGIN DAFNY and END DAFNY.
- Do not modify the original code, just fix the requires and ensures clauses.
- Do just output the Dafny code, without explanations.
- A semi-colon is not needed at the end of each requires/ensures clause.
- The requires and ensures clauses should be written after the method/function declaration and before the opening braces of the method/function body.
- Try to use sequence operations, instead of quantifiers over arrays, when possible.
- Mathematical collections in Dafny (seq, set, map, multiset) do not support dot operators (like .Map) or arithmetics.
- Before diving into writing conditions, thoroughly understand each variable's role in the algorithm and how they relate to each other, taking advantage of any explanatory comments in the code.
- Try to create separate requires clauses for each necessary precondition, and separate ensures clauses for each guaranteed postcondition."""

base_prompt = """
You are an expert in the Dafny programming language and formal verification. 
Your task is to insert only pre and post conditions (requires/ensures clauses) into the provided Dafny code, following these specific instructions with no deviations:

CRITICAL INSTRUCTIONS:
1. ⚠️ NEVER ADD NULL CHECKS ("requires x != null") for ANY parameters
   • In Dafny, reference types like array<T>, seq<T>, set<T>, map<K,V> are NON-NULLABLE by default
   • Adding "requires a != null" for arrays, sequences, sets, or maps is INCORRECT and redundant

2. NON-NULLABLE types in Dafny (NEVER add null checks for these):
   • array<T> - arrays are never null
   • seq<T> - sequences are never null
   • set<T> - sets are never null
   • map<K,V> - maps are never null
   • All value types (int, bool, etc.) are never null

3. Simple rule: Only add "requires x != null" if the type has an explicit ? symbol (like Class? or array?<int>)

Task Requirements:
- The Dafny code will be enclosed between the tags BEGIN DAFNY and END DAFNY.
- You must not modify the original code in any way. Only insert requires and ensures clauses.
- Do not provide any explanations or comments in your output. Only output the modified code with pre/post conditions.

Output Format:
- The requires and ensures clauses must appear immediately after the method/function declaration and before the method/function body braces {, as in:
   method Abs(x: int) returns (y: int)
     requires true
     ensures y >= 0
     ensures x == y || x == -y
   {
     if x < 0 { return -x; } else { return x; }
   }
- Use Dafny's correct syntax, such as:
   -- Logical implication as ==>.
   -- Sequence length as |s| and array length as a.Length.
   -- Avoid unsupported dot operations on sequences and sets like s.Map, s.Contains, s.Min, etc.

Guidelines for Writing Pre/Post Conditions:
- Do not add null checks like 'requires x != null'.
- For ensures clauses, establish what properties the returned values or output parameters satisfy.
- For requires clauses, specify necessary conditions for the method to work correctly.
- Where applicable, prefer sequence operations over quantifiers on arrays.
- Always provide explicit lower bounds in quantifiers like forall k :: 0 <= k <= n, instead of forall k :: k < n.
- You must first understand the role of each variable in the algorithm, using any comments provided, to properly construct meaningful conditions.
- Create separate requires/ensures clauses for each distinct condition rather than combining multiple conditions with logical AND (&&).
- Do not include redundant or overly generic conditions.
- When a method modifies an array ('modifies' clause), consider what parts of the array change and what parts remain unchanged.
- For functions, ensures clauses should describe what the function returns in terms of its parameters.
- For recursive functions, consider the base case and the recursive case separately.
- If a method returns a boolean, the ensures clause should specify what conditions make it return true or false.
- Ghost functions can be useful for writing complex specifications.
- When a method updates object fields, the ensures clause should describe the relationship between pre-state (old) and post-state values.
   
Failure to strictly follow these instructions will result in incorrect output.
"""

######## Global initializations ########

# create output folder
output_folder = output_folder_base + "/" + llms[0].model + " - " + str(llms[0].temperature) + " - " + time.strftime(r"%Y-%m-%d %H-%M")
os.makedirs(output_folder, exist_ok=True)

# create stripped folder
os.makedirs(stripped_folder, exist_ok=True)

# initialize the log file
log_file = open(output_folder + r"\_log.txt", "w")

# initialize the API clients
clientOpenAI = OpenAI(api_key = openai_key)
clientAnthropic = anthropic.Anthropic(api_key = antrophic_key)
clientDeepSeek = OpenAI(api_key = deepseek_key, base_url = "https://api.deepseek.com/v1")

######## Dany file merging ########

# Merges the contents of two files (represented as strings) without duplicating common lines.
# Returns the merged content as a list of lines.
def merge_files(file1, file2):
    file1_lines = file1.split('\n')
    file2_lines = file2.split('\n')
    merged_lines = []
    index1 = 0
    index2 = 0
    while index1 < len(file1_lines) and index2 < len(file2_lines):
        # get the next lines from each file to local variables
        line1 = file1_lines[index1]
        line2 = file2_lines[index2]

        # remove all whitespaces from each line
        line1_stripped = line1.strip().replace(" ","")
        line2_stripped = line2.strip().replace(" ","")
        
        # remove all characters after // in each line (in case they appear)
        if '//' in line1_stripped:
            line1_stripped = line1_stripped[:line1_stripped.index('//')]
        if '//' in line2_stripped:
            line2_stripped = line2_stripped[:line2_stripped.index('//')]
        # compare ignoring spaces and comments (lines starting with '//')
        if line1_stripped == line2_stripped:
            merged_lines.append(line1)
            index1 += 1
            index2 += 1
        elif line1.strip() == "":
            index1 += 1
            merged_lines.append("")
        elif line2.strip() == "":
            index2 += 1
            merged_lines.append("")
        else:
            # find the nearest subsequent matching line in file2
            found2 = -1
            for i in range(index2 + 1, len(file2_lines)):
                if file1_lines[index1].strip().replace(" ","") == file2_lines[i].strip().replace(" ",""):
                    found2 = i
                    break

            # find the nearest subsequent matching line in file1
            found1 = -1
            for i in range(index1 + 1, len(file1_lines)):
                if file1_lines[i].strip().replace(" ","") == file2_lines[index2].strip().replace(" ",""):
                    found1 = i
                    break
            
            if found1 == -1 and found2 == -1:
                if index1 < index2:
                    merged_lines.append(file1_lines[index1])
                    index1 += 1
                else:
                    merged_lines.append(file2_lines[index2])
                    index2 += 1
            elif found1 == -1:
                for i in range(index2, found2):
                    merged_lines.append(file2_lines[i])
                    index2 += 1
            elif found2 == -1:
                for i in range(index1, found1):
                    merged_lines.append(file1_lines[i])
                    index1 += 1
            else:
                if found1 < found2:
                    for i in range(index1, found1):
                        merged_lines.append(file1_lines[i])
                        index1 += 1
                else:
                    for i in range(index2, found2):
                        merged_lines.append(file2_lines[i])
                        index2 += 1

    if index1 < len(file1_lines):
        merged_lines.extend(file1_lines[index1:])
    if index2 < len(file2_lines):
        merged_lines.extend(file2_lines[index2:])
    return "\n".join(merged_lines)

tokens_spent = 0

######## Stripping pre/post conditions from a Dafny file ########

# Strips the requires and ensures clauses from a Dafny file and saves the result to a new file
def remove_prepost_lines_and_save(filepath):
    # Get filename from filepath
    filename = os.path.basename(filepath)

    # Determine the new filename by appending 'stripped' before the .dfy extension
    new_filename = f"{filename[:-4]}_stripped.dfy"

    # Determine the new filepath by joining the output folder and the new filename
    new_filepath = os.path.join(output_folder, new_filename)
    
    # Also save a copy in the dedicated stripped folder
    stripped_filepath = os.path.join(stripped_folder, new_filename)

    # Read the lines of the source file
    with open(filepath, 'r') as file:
        lines = file.readlines()

    # Filter out lines that contain requires or ensures keywords
    new_lines = [line for line in lines if 'requires' not in line and 'ensures' not in line]

    # Write the filtered lines to the new file in output folder
    with open(new_filepath, 'w') as new_file:
        new_file.writelines(new_lines)
        
    # Also write to the stripped folder
    with open(stripped_filepath, 'w') as stripped_file:
        stripped_file.writelines(new_lines)

    if verbose > 1:    
        print(f"Stripped file saved to {new_filepath} and {stripped_filepath}.")
    log_file.write(f"Stripped file saved to {new_filepath} and {stripped_filepath}.\n")

    return new_filepath

####### Dafny file verification #######

# Verifies a Dafny file using the Dafny verifier
def verify_dafny_file(filepath):
    # run the verifier
    process = subprocess.Popen([dafny_executable,"verify", filepath,"--verification-time-limit:" + str(verifier_timeout)], stdout=subprocess.PIPE, stderr=subprocess.PIPE) 
    stdout, stderr = process.communicate()

    # save the output messages to the log file
    log_file.write(stdout.decode('utf-8'))

    # determine outcome
    if b"resolution/type errors" in stdout or b"parse errors" in stdout:
        return -1 # syntax errors
    else:
        if stdout.decode('utf-8').strip().endswith('0 errors'):
            return 1 # success
        else:    
            return 0 # failure


####### LLM processing #######

# Processes a Dafny file using the LLM to generate pre/post conditions
def process_file(filepath, llm_data, trial_number, prev_succeeded, post_processing = True, refined_prompt = True, fix=False):
    
    time_spent_api_call = 0

    # Construct the new filename by replacing 'stripped' with 'gpt'
    if fix:
        new_filepath = filepath.replace('_merged.dfy', f"_{trial_number}_gpt.dfy" )
    else:
        new_filepath = filepath.replace('_stripped.dfy', f"_{trial_number}_gpt.dfy")
    
    # Read the file content
    with open(filepath, 'r', encoding='utf-8') as file:
        file_content = file.read()

    if refined_prompt:
        # Construct the prompt with the file content
        if fix:
            instructions_prompt = base_prompt_fix
        else:
            instructions_prompt = base_prompt
        
        # remove dynamic parts of the prompt based on the file content 
        lines = instructions_prompt.split('\n') # split the prompt into lines
        if 'function ' not in file_content:
            lines = [line for line in lines if 'function ' not in line and 'recursive function' not in line]
        if 'modifies ' not in file_content:
            lines = [line for line in lines if 'modifies' not in line]
        if 'boolean ' not in file_content and 'bool ' not in file_content:
            lines = [line for line in lines if 'boolean' not in line]
        if 'ghost ' not in file_content:
            lines = [line for line in lines if 'ghost ' not in line]
        instructions_prompt = "\n".join(lines)  # merge the lines back into a single string  
    
    else:
        instructions_prompt = minimal_prompt

    # Add the file content to the user prompt
    code_prompt = "BEGIN DAFNY\n" + file_content + "\nEND DAFNY\n"

    # save the prompt to a filename terminating in _prompt.txt
    with open(new_filepath.replace('_gpt.dfy', '_prompt.txt'), 'w', encoding='utf-8') as prompt_file:
        prompt_file.write(instructions_prompt + "\n" + code_prompt)
   
    try:
        start_time_api_call = time.time()

        # Call the OpenAI API to process the file content
        if llm_data.api == API.OpenAI:
            if llm_data.temperature == 0:
                response = clientOpenAI.chat.completions.create(
                        messages=[
                            {"role": "system", "content": instructions_prompt}, 
                            {"role": "user", "content": code_prompt}
                        ],
                        model = llm_data.model
                )            
            else:
                response = clientOpenAI.chat.completions.create(
                        messages=[
                            {"role": "system", "content": instructions_prompt}, 
                            {"role": "user", "content": code_prompt}
                        ],
                        model = llm_data.model, 
                        temperature = llm_data.temperature
                )            
            output = response.choices[0].message.content
        elif llm_data.api == API.DeepSeek:
            if llm_data.temperature == 0:
                response = clientDeepSeek.chat.completions.create(
                    messages=[
                        {"role": "system", "content": instructions_prompt}, 
                        {"role": "user", "content": code_prompt}
                    ],
                    model = llm_data.model
                )            
            else:
                response = clientDeepSeek.chat.completions.create(
                    messages=[
                        {"role": "system", "content": instructions_prompt}, 
                        {"role": "user", "content": code_prompt}
                    ],
                    model = llm_data.model,
                    temperature = llm_data.temperature
                )            
            output = response.choices[0].message.content
        elif llm_data.api == API.Antrophic:
            response = clientAnthropic.messages.create(
                model= llm_data.model,
                max_tokens=2000, #1000
                temperature = llm_data.temperature,
                system= instructions_prompt,
                messages=[
                    {"role": "user", "content": code_prompt}
                ]
            )
            output = response.content[0].text
        else:
            raise ValueError(f"Unsupported API type: {llm_data.api}")

        end_time_api_call = time.time()
        time_spent_api_call = end_time_api_call - start_time_api_call

        # Write the API's response to the new file
        with open(new_filepath, 'w', encoding='utf-8') as new_file:
            new_file.write(output)


        # extract code between delimiters in output
        if "```dafny" in output:
            # extract just the substring between "```dafny" and '```' (excluded)
            output = output[output.find("```dafny") + 8:output.rfind("```")]
        elif "```" in output:
            # extract just the substring between "```" and '```' (excluded)
            output = output[output.find("```") + 3:output.rfind("```")]
        if "BEGIN DAFNY\n" in output:
            # extract just the substring between "BEGIN DAFNY" and 'END DAFNY' (excluded)
            output = output[output.find("BEGIN DAFNY") + 12:output.rfind("END DAFNY")]

        merged_output = output

        # if first line starts in "Here" remove it
        if output.startswith("Here"):
            output = output[output.find("\n")+1:]

        if post_processing:
            # Fix problems of misplaced requires/ensures
            output_lines = output.split('\n')

            # do some cleanup
            for i in range(len(output_lines)):
                line = output_lines[i]

                # Remove ';' from the end of line of lines that start with requires or ensures
                if (line.strip().startswith('requires ') or line.strip().startswith('ensures ')) and line.strip().endswith(';'):
                    output_lines[i] = line[:-1]
                    line = output_lines[i]

                # Replace '// Req: '  with 'requires '
                if line.strip().startswith('// Req: '):
                    output_lines[i] = line.replace('// Req: ', 'requires ')
                    line = output_lines[i]
                
                # Replace '// Ens: '  with 'ensures '
                if line.strip().startswith('// Ens: '):
                    output_lines[i] = line.replace('// Ens: ', 'ensures ')
                    line = output_lines[i]

                # Replace '[..0..'  with '[..'
                if '[..0..' in line:
                    output_lines[i] = line.replace('[..0..', '[..')
                    line = output_lines[i]

                if line.strip() == "{}": # possibly erased body (removes to facilitate merge!)
                    output_lines[i] = ""
                    line = ""                    

            # solve problems of misplaced requires/ensures
            saved_conditions = []
            saved_open_brace = []
            expecting_condition = False
            missing_condition = False
            for i in range(len(output_lines)):
                line = output_lines[i]
                
                if line.strip().startswith('requires ') or line.strip().startswith('ensures '):
                    if not expecting_condition: 
                        saved_conditions.append(line)
                        output_lines[i] = ""
                    missing_condition = False

                elif line.strip().startswith('method ') or line.strip().startswith('function ') or line.strip().startswith('predicate '):
                    if saved_open_brace != []:
                        output_lines[i] = saved_open_brace[0] + "\n" + line 
                        saved_open_brace = []
                        line = output_lines[i]
                    expecting_condition = True
                    missing_condition = True
                    if saved_conditions != []:
                        # insert the saved lines after the current one, keeping the current
                        new_line = line 
                        # add the saved lines one by one
                        for saved_line in saved_conditions:
                            new_line = new_line + "\n" + saved_line 
                        saved_conditions = []
                        output_lines[i] = new_line
                        missing_condition = False

                elif line.strip() == "{" and missing_condition:
                    saved_open_brace = [line] 
                    output_lines[i] = ""

                elif line.strip() != "" and not line.strip().startswith('//'):
                    if saved_open_brace != []:
                        output_lines[i] = saved_open_brace[0] + "\n" + line 
                        saved_open_brace = []
                        line = output_lines[i]
                    expecting_condition = False
                    missing_condition = False
                    saved_conditions = []

            # Join the lines into a single string separated by newlines
            output = "\n".join(output_lines)

            merged_output = merge_files(file_content, output)


        # similar to the previous step, but for the merged output
        with open(new_filepath.replace('_gpt.dfy', '_merged.dfy'), 'w', encoding='utf-8') as new_file:
            new_file.write(merged_output)

        if verbose > 1:
            print(f"LLM output saved to {new_filepath}.\nMerged file saved to {new_filepath.replace('_gpt.dfy', '_merged.dfy')}")
        log_file.write(f"LLM output saved to {new_filepath}.\nMerged file saved to {new_filepath.replace('_gpt.dfy', '_merged.dfy')}\n")

    except Exception as e:
        print(f"Error processing {filepath}: {e}")
        log_file.write(f"Error processing {filepath}: {e}\n")
        #print stack trace
        traceback.print_exc()
        return "", 0

    return new_filepath.replace('_gpt.dfy', '_merged.dfy'), time_spent_api_call

    
# Process all Dany files in the input folder
def process_directory(refined_prompt = True, post_processing = True):
    counter = 0
    success = 0
    total_attempts = 0
    original_files_skipped = []
    failed_files = []

    # create CSV file to store the results
    results_file = open(output_folder + r"\_results.csv", "w")
    results_file.write("Filename; Attempt; Success; Time Gen; Time Ver; Time API Call; Success Merged Original\n")

    # loop through the files in the input folder
    for filename in os.listdir(input_folder):
        if filename.endswith('.dfy'):

            filepath = os.path.join(input_folder, filename)
            print(f"\nProcessing {filename}")
            log_file.write(f"Processing {filename}\n")
            succ = verify_dafny_file(filepath)

            if succ != 1:
                print(filepath)
                print(f"{filename}: Original file not verified and skipped")
                original_files_skipped.append(filename)
                continue

            # create new file with pre/post conditions removed
            new_filepath = remove_prepost_lines_and_save(filepath)

            # try a maximum number of attempts to process the file
            succeeded = 0
            succeed = False
            gpt_output_file = ""

            # loop through the LLMs in the list of llms
            for llm_data in llms:
                if succeeded > 0:
                    break
                attempts = 0
                max_attempts = llm_data.attempts
                max_failures = llm_data.max_failures
                while attempts < max_attempts:
                    if succeeded == 0 and attempts >= max_failures:
                        break
                    start_time = time.time()
                    gpt_output_file, time3 = process_file(new_filepath, llm_data, attempts+1, succeeded, refined_prompt, post_processing, False)
                    end_time = time.time()
                    time_spent = end_time - start_time
                    
                    if gpt_output_file == "":
                        continue

                    attempts += 1
                    total_attempts = total_attempts + 1
                    start_time2 = time.time()
                    succ = verify_dafny_file(gpt_output_file)
                    end_time2 = time.time()
                    time_spent2 = end_time2 - start_time2

                    if succ == 1:
                        succeed = True
                        succeeded += 1
                        succ2 = 1
                        if verbose > 0:
                            print(f"{filename}: Attempt {attempts} successful")
                    else:
                        if verbose > 0:
                            print(f"{filename}: Attempt {attempts} failed")
                        with open(filepath, 'r', encoding='utf-8') as file:
                            original_file_content = file.read()
                        with open(gpt_output_file, 'r', encoding='utf-8') as file:
                            generated_file_content = file.read()
                        merged_with_original_content = merge_files(original_file_content, generated_file_content)
                        merged_with_original_path = gpt_output_file.replace('.dfy', '_original_merged.dfy')
                        with open(merged_with_original_path, 'w', encoding='utf-8') as new_file:
                            new_file.write(merged_with_original_content)
                        succ2 = verify_dafny_file(merged_with_original_path)
        
                    # write the results to the CSV file
                    results_file.write(f"{filename}; {attempts}; {succ}; {time_spent:.4f}; {time_spent2:.4f}; {time3: .4f}; {succ2}\n")
                    results_file.flush()

            if succeed:
                print(f"{filename}: Success")
                log_file.write(f"{filename}: Success\n")
                success += 1
            else:
                print(f"{filename}: Failure")
                log_file.write(f"{filename}: Failure\n")
                failed_files.append(filename)
            counter += 1
            if verbose > 0:
                print(f"Processed so far {counter} files, {success} verified successfully in {total_attempts} attempts")
            if verbose > 0 and len(original_files_skipped) > 0:
                print(f"Original files not verified and skipped so far: {original_files_skipped}")
            
    print(f"Processed {counter} files, {success} verified successfully in {total_attempts} attempts")
    log_file.write(f"Processed {counter} files, {success} verified successfully, in {total_attempts} attempts\n")

    if len(failed_files) > 0:
        print(f"Failed files: {failed_files}")
        log_file.write(f"Failed files: {failed_files}\n")

    if len(original_files_skipped) > 0:
        print(f"Original files not verified and skipped: {original_files_skipped}")

# entry point
process_directory() 