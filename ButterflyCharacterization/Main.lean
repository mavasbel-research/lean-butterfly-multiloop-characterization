import ButterflyCharacterization.Adapters.Inbound.CliController

open ButterflyCharacterization.Adapters.Inbound

def main (args : List String) : IO UInt32 := do
  runCli args
