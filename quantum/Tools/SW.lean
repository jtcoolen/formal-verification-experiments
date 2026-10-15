def main : IO Unit := do
  let a ← IO.clockMs
  IO.println s! "ms {a}"
