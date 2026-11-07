import E11Lrat.Tri
import E11Lrat.Store

/-! # NT-E11.2: the store begins with `cnf 171 L` and ends with the empty clause -/

namespace E11Lrat

open OpenProblemsLib.LRAT

def P0 : List (List Nat) := alo 171 ++ amo 171 ++ symm 171
def P1 : List (List Nat) := (T00.map dec).map triC
def P2 : List (List Nat) := (T01.map dec).map triC
def P3 : List (List Nat) := (T02.map dec).map triC
def P4 : List (List Nat) := (T03.map dec).map triC
def P5 : List (List Nat) := (T04.map dec).map triC
def P6 : List (List Nat) := (T05.map dec).map triC
def P7 : List (List Nat) := (T06.map dec).map triC
def P8 : List (List Nat) := (T07.map dec).map triC
def P9 : List (List Nat) := (T08.map dec).map triC
def P10 : List (List Nat) := (T09.map dec).map triC
def P11 : List (List Nat) := (T10.map dec).map triC
def P12 : List (List Nat) := (T11.map dec).map triC
def P13 : List (List Nat) := (T12.map dec).map triC
def P14 : List (List Nat) := (T13.map dec).map triC
def P15 : List (List Nat) := (T14.map dec).map triC
def P16 : List (List Nat) := (T15.map dec).map triC
def P17 : List (List Nat) := (T16.map dec).map triC
def P18 : List (List Nat) := (T17.map dec).map triC
def P19 : List (List Nat) := (T18.map dec).map triC
def P20 : List (List Nat) := (T19.map dec).map triC
def P21 : List (List Nat) := (T20.map dec).map triC
def P22 : List (List Nat) := (T21.map dec).map triC
def P23 : List (List Nat) := (T22.map dec).map triC
def P24 : List (List Nat) := (T23.map dec).map triC
def P25 : List (List Nat) := (T24.map dec).map triC
def P26 : List (List Nat) := (T25.map dec).map triC
def P27 : List (List Nat) := (T26.map dec).map triC
def P28 : List (List Nat) := (T27.map dec).map triC
def P29 : List (List Nat) := (T28.map dec).map triC
def P30 : List (List Nat) := (T29.map dec).map triC
def P31 : List (List Nat) := (T30.map dec).map triC
def P32 : List (List Nat) := (T31.map dec).map triC
def P33 : List (List Nat) := (T32.map dec).map triC
def P34 : List (List Nat) := (T33.map dec).map triC
def P35 : List (List Nat) := (T34.map dec).map triC
def P36 : List (List Nat) := (T35.map dec).map triC
def P37 : List (List Nat) := (T36.map dec).map triC
def P38 : List (List Nat) := (T37.map dec).map triC
def P39 : List (List Nat) := (T38.map dec).map triC
def P40 : List (List Nat) := (T39.map dec).map triC
def P41 : List (List Nat) := (T40.map dec).map triC
def P42 : List (List Nat) := (T41.map dec).map triC
def P43 : List (List Nat) := (T42.map dec).map triC
def P44 : List (List Nat) := (T43.map dec).map triC
def P45 : List (List Nat) := (T44.map dec).map triC

theorem map_eq : L.map triC = P1 ++ (P2 ++ (P3 ++ (P4 ++ (P5 ++ (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))))))))))))))) := by
  simp only [L, List.map_append]; rfl

theorem cnf_eq : cnf 171 L = P0 ++ (P1 ++ (P2 ++ (P3 ++ (P4 ++ (P5 ++ (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))))))))))))))))) := by
  unfold cnf; rw [map_eq]; rfl

theorem len0 : P0.length = 1369 := by decide +kernel
theorem chk0 : chkF S P0 1 = true := by decide +kernel
theorem len1 : P1.length = 1000 := by decide +kernel
theorem chk1 : chkF S P1 1370 = true := by decide +kernel
theorem len2 : P2.length = 1000 := by decide +kernel
theorem chk2 : chkF S P2 2370 = true := by decide +kernel
theorem len3 : P3.length = 1000 := by decide +kernel
theorem chk3 : chkF S P3 3370 = true := by decide +kernel
theorem len4 : P4.length = 1000 := by decide +kernel
theorem chk4 : chkF S P4 4370 = true := by decide +kernel
theorem len5 : P5.length = 1000 := by decide +kernel
theorem chk5 : chkF S P5 5370 = true := by decide +kernel
theorem len6 : P6.length = 1000 := by decide +kernel
theorem chk6 : chkF S P6 6370 = true := by decide +kernel
theorem len7 : P7.length = 1000 := by decide +kernel
theorem chk7 : chkF S P7 7370 = true := by decide +kernel
theorem len8 : P8.length = 1000 := by decide +kernel
theorem chk8 : chkF S P8 8370 = true := by decide +kernel
theorem len9 : P9.length = 1000 := by decide +kernel
theorem chk9 : chkF S P9 9370 = true := by decide +kernel
theorem len10 : P10.length = 1000 := by decide +kernel
theorem chk10 : chkF S P10 10370 = true := by decide +kernel
theorem len11 : P11.length = 1000 := by decide +kernel
theorem chk11 : chkF S P11 11370 = true := by decide +kernel
theorem len12 : P12.length = 1000 := by decide +kernel
theorem chk12 : chkF S P12 12370 = true := by decide +kernel
theorem len13 : P13.length = 1000 := by decide +kernel
theorem chk13 : chkF S P13 13370 = true := by decide +kernel
theorem len14 : P14.length = 1000 := by decide +kernel
theorem chk14 : chkF S P14 14370 = true := by decide +kernel
theorem len15 : P15.length = 1000 := by decide +kernel
theorem chk15 : chkF S P15 15370 = true := by decide +kernel
theorem len16 : P16.length = 1000 := by decide +kernel
theorem chk16 : chkF S P16 16370 = true := by decide +kernel
theorem len17 : P17.length = 1000 := by decide +kernel
theorem chk17 : chkF S P17 17370 = true := by decide +kernel
theorem len18 : P18.length = 1000 := by decide +kernel
theorem chk18 : chkF S P18 18370 = true := by decide +kernel
theorem len19 : P19.length = 1000 := by decide +kernel
theorem chk19 : chkF S P19 19370 = true := by decide +kernel
theorem len20 : P20.length = 1000 := by decide +kernel
theorem chk20 : chkF S P20 20370 = true := by decide +kernel
theorem len21 : P21.length = 1000 := by decide +kernel
theorem chk21 : chkF S P21 21370 = true := by decide +kernel
theorem len22 : P22.length = 1000 := by decide +kernel
theorem chk22 : chkF S P22 22370 = true := by decide +kernel
theorem len23 : P23.length = 1000 := by decide +kernel
theorem chk23 : chkF S P23 23370 = true := by decide +kernel
theorem len24 : P24.length = 1000 := by decide +kernel
theorem chk24 : chkF S P24 24370 = true := by decide +kernel
theorem len25 : P25.length = 1000 := by decide +kernel
theorem chk25 : chkF S P25 25370 = true := by decide +kernel
theorem len26 : P26.length = 1000 := by decide +kernel
theorem chk26 : chkF S P26 26370 = true := by decide +kernel
theorem len27 : P27.length = 1000 := by decide +kernel
theorem chk27 : chkF S P27 27370 = true := by decide +kernel
theorem len28 : P28.length = 1000 := by decide +kernel
theorem chk28 : chkF S P28 28370 = true := by decide +kernel
theorem len29 : P29.length = 1000 := by decide +kernel
theorem chk29 : chkF S P29 29370 = true := by decide +kernel
theorem len30 : P30.length = 1000 := by decide +kernel
theorem chk30 : chkF S P30 30370 = true := by decide +kernel
theorem len31 : P31.length = 1000 := by decide +kernel
theorem chk31 : chkF S P31 31370 = true := by decide +kernel
theorem len32 : P32.length = 1000 := by decide +kernel
theorem chk32 : chkF S P32 32370 = true := by decide +kernel
theorem len33 : P33.length = 1000 := by decide +kernel
theorem chk33 : chkF S P33 33370 = true := by decide +kernel
theorem len34 : P34.length = 1000 := by decide +kernel
theorem chk34 : chkF S P34 34370 = true := by decide +kernel
theorem len35 : P35.length = 1000 := by decide +kernel
theorem chk35 : chkF S P35 35370 = true := by decide +kernel
theorem len36 : P36.length = 1000 := by decide +kernel
theorem chk36 : chkF S P36 36370 = true := by decide +kernel
theorem len37 : P37.length = 1000 := by decide +kernel
theorem chk37 : chkF S P37 37370 = true := by decide +kernel
theorem len38 : P38.length = 1000 := by decide +kernel
theorem chk38 : chkF S P38 38370 = true := by decide +kernel
theorem len39 : P39.length = 1000 := by decide +kernel
theorem chk39 : chkF S P39 39370 = true := by decide +kernel
theorem len40 : P40.length = 1000 := by decide +kernel
theorem chk40 : chkF S P40 40370 = true := by decide +kernel
theorem len41 : P41.length = 1000 := by decide +kernel
theorem chk41 : chkF S P41 41370 = true := by decide +kernel
theorem len42 : P42.length = 1000 := by decide +kernel
theorem chk42 : chkF S P42 42370 = true := by decide +kernel
theorem len43 : P43.length = 1000 := by decide +kernel
theorem chk43 : chkF S P43 43370 = true := by decide +kernel
theorem len44 : P44.length = 1000 := by decide +kernel
theorem chk44 : chkF S P44 44370 = true := by decide +kernel
theorem len45 : P45.length = 526 := by decide +kernel
theorem chk45 : chkF S P45 45370 = true := by decide +kernel

theorem chain45 : chkF S P45 45370 = true := chk45
theorem chain44 : chkF S (P44 ++ (P45)) 44370 = true := by
  rw [chkF_append, chk44, len44, Bool.true_and]; exact chain45
theorem chain43 : chkF S (P43 ++ (P44 ++ (P45))) 43370 = true := by
  rw [chkF_append, chk43, len43, Bool.true_and]; exact chain44
theorem chain42 : chkF S (P42 ++ (P43 ++ (P44 ++ (P45)))) 42370 = true := by
  rw [chkF_append, chk42, len42, Bool.true_and]; exact chain43
theorem chain41 : chkF S (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))) 41370 = true := by
  rw [chkF_append, chk41, len41, Bool.true_and]; exact chain42
theorem chain40 : chkF S (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))) 40370 = true := by
  rw [chkF_append, chk40, len40, Bool.true_and]; exact chain41
theorem chain39 : chkF S (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))) 39370 = true := by
  rw [chkF_append, chk39, len39, Bool.true_and]; exact chain40
theorem chain38 : chkF S (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))) 38370 = true := by
  rw [chkF_append, chk38, len38, Bool.true_and]; exact chain39
theorem chain37 : chkF S (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))) 37370 = true := by
  rw [chkF_append, chk37, len37, Bool.true_and]; exact chain38
theorem chain36 : chkF S (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))) 36370 = true := by
  rw [chkF_append, chk36, len36, Bool.true_and]; exact chain37
theorem chain35 : chkF S (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))) 35370 = true := by
  rw [chkF_append, chk35, len35, Bool.true_and]; exact chain36
theorem chain34 : chkF S (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))) 34370 = true := by
  rw [chkF_append, chk34, len34, Bool.true_and]; exact chain35
theorem chain33 : chkF S (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))) 33370 = true := by
  rw [chkF_append, chk33, len33, Bool.true_and]; exact chain34
theorem chain32 : chkF S (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))) 32370 = true := by
  rw [chkF_append, chk32, len32, Bool.true_and]; exact chain33
theorem chain31 : chkF S (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))) 31370 = true := by
  rw [chkF_append, chk31, len31, Bool.true_and]; exact chain32
theorem chain30 : chkF S (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))) 30370 = true := by
  rw [chkF_append, chk30, len30, Bool.true_and]; exact chain31
theorem chain29 : chkF S (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))) 29370 = true := by
  rw [chkF_append, chk29, len29, Bool.true_and]; exact chain30
theorem chain28 : chkF S (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))) 28370 = true := by
  rw [chkF_append, chk28, len28, Bool.true_and]; exact chain29
theorem chain27 : chkF S (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))) 27370 = true := by
  rw [chkF_append, chk27, len27, Bool.true_and]; exact chain28
theorem chain26 : chkF S (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))) 26370 = true := by
  rw [chkF_append, chk26, len26, Bool.true_and]; exact chain27
theorem chain25 : chkF S (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))) 25370 = true := by
  rw [chkF_append, chk25, len25, Bool.true_and]; exact chain26
theorem chain24 : chkF S (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))) 24370 = true := by
  rw [chkF_append, chk24, len24, Bool.true_and]; exact chain25
theorem chain23 : chkF S (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))) 23370 = true := by
  rw [chkF_append, chk23, len23, Bool.true_and]; exact chain24
theorem chain22 : chkF S (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))) 22370 = true := by
  rw [chkF_append, chk22, len22, Bool.true_and]; exact chain23
theorem chain21 : chkF S (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))) 21370 = true := by
  rw [chkF_append, chk21, len21, Bool.true_and]; exact chain22
theorem chain20 : chkF S (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))) 20370 = true := by
  rw [chkF_append, chk20, len20, Bool.true_and]; exact chain21
theorem chain19 : chkF S (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))) 19370 = true := by
  rw [chkF_append, chk19, len19, Bool.true_and]; exact chain20
theorem chain18 : chkF S (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))) 18370 = true := by
  rw [chkF_append, chk18, len18, Bool.true_and]; exact chain19
theorem chain17 : chkF S (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))) 17370 = true := by
  rw [chkF_append, chk17, len17, Bool.true_and]; exact chain18
theorem chain16 : chkF S (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))) 16370 = true := by
  rw [chkF_append, chk16, len16, Bool.true_and]; exact chain17
theorem chain15 : chkF S (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))) 15370 = true := by
  rw [chkF_append, chk15, len15, Bool.true_and]; exact chain16
theorem chain14 : chkF S (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))) 14370 = true := by
  rw [chkF_append, chk14, len14, Bool.true_and]; exact chain15
theorem chain13 : chkF S (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))))) 13370 = true := by
  rw [chkF_append, chk13, len13, Bool.true_and]; exact chain14
theorem chain12 : chkF S (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))))) 12370 = true := by
  rw [chkF_append, chk12, len12, Bool.true_and]; exact chain13
theorem chain11 : chkF S (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))))))) 11370 = true := by
  rw [chkF_append, chk11, len11, Bool.true_and]; exact chain12
theorem chain10 : chkF S (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))))))) 10370 = true := by
  rw [chkF_append, chk10, len10, Bool.true_and]; exact chain11
theorem chain9 : chkF S (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))))))))) 9370 = true := by
  rw [chkF_append, chk9, len9, Bool.true_and]; exact chain10
theorem chain8 : chkF S (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))))))))) 8370 = true := by
  rw [chkF_append, chk8, len8, Bool.true_and]; exact chain9
theorem chain7 : chkF S (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))))))))))) 7370 = true := by
  rw [chkF_append, chk7, len7, Bool.true_and]; exact chain8
theorem chain6 : chkF S (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))))))))))) 6370 = true := by
  rw [chkF_append, chk6, len6, Bool.true_and]; exact chain7
theorem chain5 : chkF S (P5 ++ (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))))))))))))) 5370 = true := by
  rw [chkF_append, chk5, len5, Bool.true_and]; exact chain6
theorem chain4 : chkF S (P4 ++ (P5 ++ (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))))))))))))) 4370 = true := by
  rw [chkF_append, chk4, len4, Bool.true_and]; exact chain5
theorem chain3 : chkF S (P3 ++ (P4 ++ (P5 ++ (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))))))))))))))) 3370 = true := by
  rw [chkF_append, chk3, len3, Bool.true_and]; exact chain4
theorem chain2 : chkF S (P2 ++ (P3 ++ (P4 ++ (P5 ++ (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))))))))))))))) 2370 = true := by
  rw [chkF_append, chk2, len2, Bool.true_and]; exact chain3
theorem chain1 : chkF S (P1 ++ (P2 ++ (P3 ++ (P4 ++ (P5 ++ (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45))))))))))))))))))))))))))))))))))))))))))))) 1370 = true := by
  rw [chkF_append, chk1, len1, Bool.true_and]; exact chain2
theorem chain0 : chkF S (P0 ++ (P1 ++ (P2 ++ (P3 ++ (P4 ++ (P5 ++ (P6 ++ (P7 ++ (P8 ++ (P9 ++ (P10 ++ (P11 ++ (P12 ++ (P13 ++ (P14 ++ (P15 ++ (P16 ++ (P17 ++ (P18 ++ (P19 ++ (P20 ++ (P21 ++ (P22 ++ (P23 ++ (P24 ++ (P25 ++ (P26 ++ (P27 ++ (P28 ++ (P29 ++ (P30 ++ (P31 ++ (P32 ++ (P33 ++ (P34 ++ (P35 ++ (P36 ++ (P37 ++ (P38 ++ (P39 ++ (P40 ++ (P41 ++ (P42 ++ (P43 ++ (P44 ++ (P45)))))))))))))))))))))))))))))))))))))))))))))) 1 = true := by
  rw [chkF_append, chk0, len0, Bool.true_and]; exact chain1

theorem cnf_length : (cnf 171 L).length = 45895 := by
  rw [cnf_eq]; simp only [List.length_append, len0, len1, len2, len3, len4, len5, len6, len7, len8, len9, len10, len11, len12, len13, len14, len15, len16, len17, len18, len19, len20, len21, len22, len23, len24, len25, len26, len27, len28, len29, len30, len31, len32, len33, len34, len35, len36, len37, len38, len39, len40, len41, len42, len43, len44, len45]

theorem store_cnf : chkF S (cnf 171 L) 1 = true := by
  rw [cnf_eq]; exact chain0

theorem store_last : lastEmpty S 233407 = true := by decide +kernel

end E11Lrat
