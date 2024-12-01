partial def IO.allStdin : IO ByteArray := do
  let stdin ← IO.getStdin
  let rec
    go data := do
      let buf ← stdin.read 1024
      if buf.isEmpty then return data else go (data ++ buf)
  go .empty
