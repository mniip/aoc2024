import Aoc2024.Parse

partial def IO.allStdin : IO ByteArray := do
  let stdin ← IO.getStdin
  let rec
    go data := do
      let buf ← stdin.read 1024
      if buf.isEmpty then return data else go (data ++ buf)
  go .empty

def IO.main [ToString β₁] [ToString β₂]
  (parser : Parser α) (solution1 : α → β₁) (solution2 : α → β₂)
  : IO Unit
  := do
    match parser.parse (← IO.allStdin) with
    | none => IO.eprintln "Parse error"
    | some input =>
      IO.println $ solution1 input
      IO.println $ solution2 input
