-- Lists the constants of the unpruned PNT port reachable from `chebyshev_asymptotic`;
-- run with `lake env lean` and save the output to `gen/pnt_reach.txt` (used by `port_pnt.py`).
import Zeta5.PNTPort.Consequences
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut stack := #[`Zeta5.PNTPort.chebyshev_asymptotic]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do
        if !seen.contains c then stack := stack.push c
  let mut out := #[]
  for n in seen do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`Zeta5.PNTPort).isPrefixOf m then out := out.push s!"{m} {n}"
  -- also declarations in the current file's imports that are the chunk heads
  for s in out.qsort (· < ·) do IO.println s
