import tempfile
import json
import sys
import subprocess
import os
import re


def idealMemM2(cmd):

    # Create a temporary file
    with tempfile.NamedTemporaryFile(suffix=".m2", mode="w", delete=False) as temp_file:
        temp_file.write(cmd)
        temp_file_path = temp_file.name

    try:
        # Run M2 command and capture output
        result = subprocess.run(
            f"/Applications/Macaulay2-1.21/bin/M2 < {temp_file_path}",
            shell=True,
            capture_output=True,
            text=True,
        )
        # print(result.stdout)
        is_valid = False
        if "o5 = 0" in result.stdout:
            is_valid = True
        else:
            is_valid = False

        construction = ""
        found_o6 = False
        for i, line in enumerate(result.stdout.splitlines()):
            if found_o6:
                if not line.strip():  # Empty line
                    break
                construction += line + "\n"
            elif line.strip().startswith("o6 ="):
                found_o6 = True
                construction += line.replace("o6 =", "") + "\n"

        if not found_o6:
            is_valid = False
            construction = ""
        else:
            construction = construction.rstrip()  # Remove trailing newline
        # print(f"Extracted construction: {construction}")

        if is_valid:

            # better_grob = grob[1:-1].strip().split(" ")
            better_constr = construction.strip().split("\n")

            paired = []
            for i in range(len(better_constr)):

                constr_part = re.search(r"\|\s*(.*?)\s*\|", better_constr[i])
                constr_value = constr_part.group(1) if constr_part else better_constr[i]
                paired.append(constr_value)
            # for i in range(len(better_grob)):

            #     # get idx of ideal generator corresponding to the curr grob elem
            #     idx = ideal.index(better_grob[i].strip())

            #     # Extract the content between pipe symbols (e.g., get "x0^2" from "{1} | x0^2 |")
            #     constr_part = re.search(r"\|\s*(.*?)\s*\|", better_constr[i])
            #     constr_value = constr_part.group(1) if constr_part else better_constr[i]
            #     paired.append(
            #         {"grob": better_grob[i], "const": constr_value, "gen_idx": idx}
            #     )
            # print(f"paired: {paired} : {type(paired)}")
            return json.dumps(paired)
        else:
            return ""

    finally:
        # Clean up the temporary file
        os.unlink(temp_file_path)


# testCmd = """R = QQ[x,y]
# I = ideal(x)
# G = groebnerBasis I
# f = x^2*y + 3*x*y

# f % G"""

if __name__ == "__main__":
    cmd_json = sys.argv[1:]
    cmd = json.loads(" ".join(cmd_json))

    out = idealMemM2(cmd)
    print(out)
