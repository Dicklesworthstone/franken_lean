mutual
  partial def ping (n : Nat) : Nat := if n == 0 then 7 else pong (n - 1)
  partial def pong (n : Nat) : Nat := if n == 0 then 13 else ping (n - 1)
end
