#eval (ByteArray.mk #[104, 105]).size
#eval (ByteArray.mk #[104, 105]).get 0
#eval ((ByteArray.mk #[104, 105]).push 255).size
#eval (ByteArray.mk #[104, 98]).set! 1 42
#eval ByteArray.beq (ByteArray.mk #[1, 2]) (ByteArray.mk #[1, 2])
#eval ByteArray.beq (ByteArray.mk #[1]) (ByteArray.mk #[2])
#eval ByteArray.data (ByteArray.mk #[72, 105])
#eval (ByteArray.emptyWithCapacity 8).size
#eval (ByteArray.mk #[195, 169]).validateUTF8
#eval (ByteArray.mk #[192, 128]).validateUTF8
