import SciLean
import Lean.Data.Json.Basic

open Lean


def idealMemM2 (cmd: String) : IO Bool := do

  let payload :Json := Json.str cmd

  let output ← IO.Process.output {
    cmd := "python3"
    args := #["LeanM2/toM2.py", payload.compress]
    stdin := .piped
  }
  -- IO.println s!"Output: [{output.stdout}]"
  -- IO.println s!"Error: [{output.stderr}]"
  return output.stdout.trim == "True"


def idealMemM2' (cmd: String) : IO (Option (Array (String × String× Nat))) := do

  let payload :Json := Json.str cmd

  let output ← IO.Process.output {
    cmd := "python3"
    args := #["LeanM2/toM2.py", payload.compress]
    stdin := .piped
  }
  IO.println s!"Output: [{output.stdout}]"
  IO.println s!"Error: [{output.stderr}]"

  let m2Out := if output.stdout.trim == "" then none
    else
      let raw? := Json.parse output.stdout |>.toOption
      let res := match raw? with
        | some raw => (
          let arr := raw.getArr?.toOption.getD #[]

          let output := arr.map (fun item =>
              (item.getObjValD "grob" |>.getStr?.toOption.getD "UH OH",
              item.getObjValD "const" |>.getStr?.toOption.getD "UH OH",
              item.getObjValD "gen_idx" |>.getNat?.toOption.getD 0)
            )
          some output
          )
        | none => none
    res

  return m2Out


def testCmd: String := "R=QQ[x0, x1, x2]
f=((x0)^2 + x1)
I=ideal((x0)^2,x1)
G=groebnerBasis I
f % G
f//G"



#eval idealMemM2' testCmd
