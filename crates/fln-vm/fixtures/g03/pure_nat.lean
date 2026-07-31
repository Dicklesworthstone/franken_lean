-- G0-3 parity corpus: pure computation incl. the bignum path.
#eval 2 + 3 * 4
#eval (10^30 + 1) % 7
#eval Nat.fold 20 (fun i _ acc => acc + i * i) 0
#eval List.range 10 |>.map (· * 3) |>.foldl (· + ·) 0
