def affine (x slope : Float) : Float := x * slope + 0.5
def choose (flag : Bool) (x y : Float32) : Float32 := if flag then x else y

#eval affine 2.5 4.0
#eval choose true (1.5 + 2.25) (9.0 / 2.0)
#eval let offset : Float := 0.5; let f := fun (x : Float) => x + offset; f 2.0 + f 3.0
#eval let apply := fun (f : Float32 -> Float32) => f 2.5; apply (fun x => -x / 2.0)
