#eval "héllo".push '!'
#eval (String.Pos.Raw.next "héllo" ⟨1⟩).byteIdx
#eval (String.Pos.Raw.next "héllo" ⟨0⟩).byteIdx
#eval (String.Pos.Raw.prev "héllo" ⟨3⟩).byteIdx
#eval (String.Pos.Raw.prev "héllo" ⟨0⟩).byteIdx
#eval String.Pos.Raw.extract "héllo" ⟨1⟩ ⟨3⟩
#eval String.Pos.Raw.extract "héllo" ⟨1⟩ ⟨2⟩
#eval String.Pos.Raw.extract "héllo" ⟨9⟩ ⟨12⟩
#eval "hello".capitalize
#eval "élan".capitalize
#eval "".capitalize
#eval String.isPrefixOf "hél" "héllo"
#eval String.isPrefixOf "helo" "héllo"
#eval "héllo".contains 'é'
#eval "".isEmpty
#eval "x".isEmpty
