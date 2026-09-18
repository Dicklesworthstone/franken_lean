import Library.Records
open Library
def packet : Packet := { value := 9 }
theorem projected : wrap packet.value = 9 := by simp [packet]
