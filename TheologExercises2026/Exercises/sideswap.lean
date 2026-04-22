
def List.valid_sideswap : List Nat → Bool :=
fun p => ((p.sum / p.length) != 0 -- gcd benutzen
      && ((p.zip (List.range p.length)).map (fun t => (t.fst + t.snd) % p.length)).eraseDups.length == p.length)

#eval [5,1,3].valid_sideswap
#eval [5,3,1].valid_sideswap
#eval [3,1,2,2,2].valid_sideswap
