import tempfile
import json
import sys
import subprocess
import os


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

        if "o5 = 0" in result.stdout:
            return True
        else:
            # print("Output:", result.stderr)
            return False

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
