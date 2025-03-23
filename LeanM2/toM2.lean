import SciLean
import Lean.Data.Json.Basic

open Lean

def idealMemM2 (cmd: String) : IO Bool := do
  let tempFile ← IO.Process.output { cmd := "mktemp" }
  IO.println s!"Temp file created at: {tempFile.stdout}"
  let tempFilePath := tempFile.stdout.trim
  -- try
  IO.FS.writeFile tempFilePath cmd
  let output ← IO.Process.output {
    cmd := "/Applications/Macaulay2-1.21/bin/M2"
    -- args := #["<", tempFilePath, "|"  , "grep", "o5 = 0"]
    args := #["--script", tempFilePath]

    stdin := .piped
  }
  let result := output.stdout.isEmpty
  IO.println s!"Output: [{output.stdout}]"
  IO.println s!"Error: [{output.stderr}]"
  return not result
  -- finally
  --   IO.FS.removeFile tempFilePath



def idealMemM2' (cmd: String) : IO Bool := do

  let payload :Json := Json.str cmd

  let output ← IO.Process.output {
    cmd := "python3"
    args := #["LeanM2/toM2.py", payload.compress]
    stdin := .piped
  }
  -- IO.println s!"Output: [{output.stdout}]"
  -- IO.println s!"Error: [{output.stderr}]"
  return output.stdout.trim == "True"


def testCmd: String := "R = QQ[x,y]
I = ideal(x)
G = groebnerBasis I
f = x^2*y + 3*x*y

f % G"



#eval idealMemM2' testCmd
