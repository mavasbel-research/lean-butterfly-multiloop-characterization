/-!
# CLI tests (live tier, run by `lake exe run_tests`)

Runs the built `butterfly_cli` executable as a separate process and checks its output and
exit code. Requires `lake build butterfly_cli` first.
-/

namespace Tests.Live

def cli : String := ".lake/build/bin/butterfly_cli"

def runCli (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := cli, args }

def check (label : String) (ok : Bool) : IO Bool := do
  IO.println s!"[LIVE] {if ok then "PASS" else "FAIL"}: {label}"
  return ok

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length ≥ 2

def run : IO Bool := do
  let a ← runCli #["two-relay", "-1", "1", "1000"]
  let c1 ← check "two-relay: exit 0, formula area 0, simulated 0.002728"
    (a.exitCode == 0 && contains a.stdout "area, formula    : 0.000000" &&
      contains a.stdout "area, simulated  : 0.002728")
  let b ← runCli #["reflected-pair", "-0.5", "2.5"]
  let c2 ← check "reflected-pair on [-0.5, 2.5]: formula area -4 (paper's Cor. 3.4 input rule)"
    (b.exitCode == 0 && contains b.stdout "area, formula    : -4.000000")
  let c ← runCli #["list"]
  let c3 ← check "list prints the three ensembles"
    (c.exitCode == 0 && c.stdout == "two-relay\nreflected-pair\npositive\n")
  let d ← runCli #["nope", "-1", "1"]
  let c4 ← check "unknown ensemble: exit 1, message on stderr"
    (d.exitCode == 1 && d.stderr == "unknown ensemble: nope\n")
  let e ← runCli #["two-relay", "1", "-1"]
  let c5 ← check "u_min ≥ u_max rejected"
    (e.exitCode == 1 && e.stderr == "u_min must be smaller than u_max\n")
  let f ← runCli #["two-relay", "-1", "1", "3"]
  let c6 ← check "fewer than 4 samples rejected"
    (f.exitCode == 1 && f.stderr == "samples must be at least 4\n")
  let g ← runCli #["two-relay", "x", "1"]
  let c7 ← check "unparsable number prints usage" (g.exitCode == 1 && g.stderr.startsWith "usage:")
  let h ← runCli #[]
  let c8 ← check "no arguments prints usage" (h.exitCode == 1 && h.stderr.startsWith "usage:")
  return c1 && c2 && c3 && c4 && c5 && c6 && c7 && c8

end Tests.Live
