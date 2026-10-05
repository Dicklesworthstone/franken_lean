prelude
import Init.Data.Cast
import Init.Data.Option.Coe
import Init.Data.Zero

theorem keep (P : Prop) (h : P) : P := h
