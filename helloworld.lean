def getGreeting (name: String) := s!"Hello, {name}! Lean is great!!!"

def main : IO Unit :=
  let names := ["Penrose", "Dirac", "Nash"]
  let greetings := names.map getGreeting
  for greeting in greetings do
    IO.println greeting
