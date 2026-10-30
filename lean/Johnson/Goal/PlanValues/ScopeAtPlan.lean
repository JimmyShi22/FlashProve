-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/PlanValues/ScopeAtPlan.lean: at every three public files in the scope of the goals
(VerifierAndGoals.InScope, Ladder.lean), the key's sizes in what the program computes from the files are what
the planner's sizing returns at the full size's written 32 lines and ten written sizes of the model.
So the records of the key file's two lookups are the two written records, at every file in scope.

The scope fixes the layout file and the parameter file but for eight numbers, and leaves the scale
file free. So an equation at the stored example's files alone would speak of one member of the
scope. The key's sizes read neither the eight numbers nor the scale file nor the layout file: they
are Plan.keySized at the parameter file's first 32 lines and at what follows from the layout of the
committed matrix, which is made from ten numbers: the lines D, L, d, dh, f, fe, NE, V, and H dh and
G dh. Here that is proved, along the program's own text.

Main names.
  restText v, policy_eq   the parameter file at the free numbers v: the 32 lines, then restText v.
  readLines_policy        the reader of the 32 lines gives Params.recordLines and leaves restText v.
  rest_bytes              restText v begins with twelve written lines, four lines "name number"
                          with free numbers, and 56 written lines.
  polWord_A1, polWord_D   what the reader by name finds there for eleven names.
  scan_sizes              so the strict scan's record has these eleven numbers, where it returns.
  layout_sizes, polLayout_layout, pubOf_wsLay, publicOf_wsLay, shapesOf_ranges
                          the program's steps from the scan to what the key's proof of the ranges
                          looks up, taken apart by name.
  key_at_policy           at the parameter file at any v, any scale file and any layout file.
  key_at_scope, pubs_at_scope   at every three files in scope.

Limits. One direction: from a program that returns (Model.Verify.planned = .ok p): that it returns
at a file in scope is not shown here. Of the key's sizes only the lookups are then held against
written values (Johnson/Top/H/LooksAtPlan.lean). That a description of the protocol takes its
numbers from Model.Verify.planned is not said here. The statements speak of what the planner made
(p.chains.made.sized.key), not of what a check reads back from a chain's parameter bytes
(p.chains.key). Nothing on soundness.
-/
import Johnson.Top.H.LooksAtPlan
import OnBytes.Tie.Pv.KeyLookup.ScanText
import OnBytes.K.Left.SaysLinesPrefix
import OnBytes.Model.Fit.PlannedParts
import Ladder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind recordLines)
open OnBytes.K.Left (keeps_lines toList_data)
open OnBytes.K.Left.TestSaysLines (full32)

/-! ## 1. The parameter file at free numbers -/

/-- What stands behind the 32 lines in VerifierAndGoals.policyFile v. -/
def restText (v : VerifierAndGoals.FreeLines) : String :=
  VerifierAndGoals.behindA1 ++
    s!"eps1_lo {v.eps1 % 2 ^ 32}\neps1_hi {v.eps1 / 2 ^ 32}\n" ++
    s!"eps2_lo {v.eps2 % 2 ^ 32}\neps2_hi {v.eps2 / 2 ^ 32}\n" ++ VerifierAndGoals.behindA2 ++
    s!"MF {v.MF}\nKF {v.KF}\n" ++
    s!"epsF_lo {v.epsF % 2 ^ 32}\nepsF_hi {v.epsF / 2 ^ 32}\n" ++ VerifierAndGoals.behindA3 ++
    s!"C {v.C}\ntheta {v.theta}\ncap {v.cap}\n" ++ VerifierAndGoals.behindB

theorem lines32_eq : VerifierAndGoals.lines32 = full32 := by decide +kernel

theorem policy_eq (v : VerifierAndGoals.FreeLines) :
    VerifierAndGoals.policyFile v = K.Left.TestSaysLines.bytesOf full32 ++ (restText v).toUTF8 := by
  rw [← lines32_eq]
  rfl

set_option maxRecDepth 100000 in
/-- The reader of the 32 lines on these lines alone: the written lines, and nothing is left. -/
theorem lines_full32 : (Params.lines (K.Left.TestSaysLines.bytesOf full32).toList).toOption =
    some (recordLines, []) := by decide +kernel

/-- On the 32 lines and any bytes behind them: the written lines, and these bytes are left. -/
theorem readLines_policy (r : ByteArray) :
    Params.readLines (K.Left.TestSaysLines.bytesOf full32 ++ r) =
      .ok (recordLines, ⟨r.toList.toArray⟩) := by
  have e : (K.Left.TestSaysLines.bytesOf full32 ++ r).toList =
      (K.Left.TestSaysLines.bytesOf full32).toList ++ r.toList := by
    rw [toList_data, toList_data, toList_data, ByteArray.data_append, Array.toList_append]
  have h0 := lines_full32
  cases hl : Params.lines (K.Left.TestSaysLines.bytesOf full32).toList with
  | error x =>
    rw [hl] at h0
    cases h0
  | ok p =>
    rw [hl] at h0
    have hp : p = (recordLines, []) := Option.some.inj h0
    rw [hp] at hl
    unfold Params.readLines
    rw [e, keeps_lines _ _ r.toList _ hl]
    rfl

/-- The reader by name on the parameter file searches the lines of restText v. -/
theorem polWord_policy (v : VerifierAndGoals.FreeLines) (n : String) :
    polWord (VerifierAndGoals.policyFile v) n = findWord n (linesOf (bytesOf (restText v))) := by
  unfold polWord
  rw [policy_eq, readLines_policy]
  show findWord n (linesOf (ByteArray.mk (restText v).toUTF8.toList.toArray).toList) = _
  rw [toList_data]
  rfl

/-! ## 2. The text behind the 32 lines, in pieces -/

theorem lit0 : bytesOf (toString "eps1_lo ") = bytesOf "eps1_lo" ++ [0x20] := by decide +kernel
theorem lit1 : bytesOf (toString "\neps1_hi ") = [0x0A] ++ (bytesOf "eps1_hi" ++ [0x20]) := by
  decide +kernel
theorem lit2 : bytesOf (toString "eps2_lo ") = bytesOf "eps2_lo" ++ [0x20] := by decide +kernel
theorem lit3 : bytesOf (toString "\neps2_hi ") = [0x0A] ++ (bytesOf "eps2_hi" ++ [0x20]) := by
  decide +kernel
theorem lit4 : bytesOf (toString "\n") = [0x0A] := by decide +kernel

/-- restText v begins with the twelve lines of VerifierAndGoals.behindA1, four lines with free numbers and the
56 lines of VerifierAndGoals.behindA2. -/
theorem rest_bytes (v : VerifierAndGoals.FreeLines) : ∃ U, bytesOf (restText v) =
    bytesOf VerifierAndGoals.behindA1 ++ (valLine "eps1_lo" (v.eps1 % 2 ^ 32) ++
      (valLine "eps1_hi" (v.eps1 / 2 ^ 32) ++ (valLine "eps2_lo" (v.eps2 % 2 ^ 32) ++
        (valLine "eps2_hi" (v.eps2 / 2 ^ 32) ++ (bytesOf VerifierAndGoals.behindA2 ++ U))))) := by
  refine ⟨bytesOf s!"MF {v.MF}\nKF {v.KF}\n" ++
    (bytesOf s!"epsF_lo {v.epsF % 2 ^ 32}\nepsF_hi {v.epsF / 2 ^ 32}\n" ++
      (bytesOf VerifierAndGoals.behindA3 ++ (bytesOf s!"C {v.C}\ntheta {v.theta}\ncap {v.cap}\n" ++
        bytesOf VerifierAndGoals.behindB))), ?_⟩
  unfold restText valLine
  simp only [bytes_append, lit0, lit1, lit2, lit3, lit4, List.append_assoc]

theorem wholeA1 : (bytesOf VerifierAndGoals.behindA1).getLast? = some 0x0A := by decide +kernel
theorem wholeA2 : (bytesOf VerifierAndGoals.behindA2).getLast? = some 0x0A := by decide +kernel

theorem atA1_prof : findWord "prof" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 20 := by
  decide +kernel
theorem atA1_L : findWord "L" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 48 := by decide +kernel
theorem atA1_d : findWord "d" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 5120 := by decide +kernel
theorem atA1_H : findWord "H" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 40 := by decide +kernel
theorem atA1_G : findWord "G" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 8 := by decide +kernel
theorem atA1_dh : findWord "dh" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 128 := by decide +kernel
theorem atA1_f : findWord "f" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 16384 := by decide +kernel
theorem atA1_fe : findWord "fe" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 8192 := by decide +kernel
theorem atA1_NE : findWord "NE" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 128 := by decide +kernel
theorem atA1_V : findWord "V" (linesOf (bytesOf VerifierAndGoals.behindA1)) = some 202048 := by decide +kernel
theorem missA1_D : (linesOf (bytesOf VerifierAndGoals.behindA1)).all (missB "D") = true := by decide +kernel
theorem atA2_D : findWord "D" (linesOf (bytesOf VerifierAndGoals.behindA2)) = some 2048 := by decide +kernel
theorem bytes_D : bytesOf "D" = [0x44] := by decide +kernel
theorem bytes_eps1_lo : bytesOf "eps1_lo" = [0x65, 0x70, 0x73, 0x31, 0x5F, 0x6C, 0x6F] := by
  decide +kernel
theorem bytes_eps1_hi : bytesOf "eps1_hi" = [0x65, 0x70, 0x73, 0x31, 0x5F, 0x68, 0x69] := by
  decide +kernel
theorem bytes_eps2_lo : bytesOf "eps2_lo" = [0x65, 0x70, 0x73, 0x32, 0x5F, 0x6C, 0x6F] := by
  decide +kernel
theorem bytes_eps2_hi : bytesOf "eps2_hi" = [0x65, 0x70, 0x73, 0x32, 0x5F, 0x68, 0x69] := by
  decide +kernel

/-- A name that is found in the twelve written lines is found on the whole file. -/
theorem polWord_A1 (v : VerifierAndGoals.FreeLines) {n : String} {x : ℕ}
    (h : findWord n (linesOf (bytesOf VerifierAndGoals.behindA1)) = some x) :
    polWord (VerifierAndGoals.policyFile v) n = some x := by
  obtain ⟨U, e⟩ := rest_bytes v
  rw [polWord_policy, e, linesOf_append wholeA1]
  exact findWord_append_some n _ _ x h

/-- No byte of the list is a line feed, from the test. -/
theorem noFeed_of {l : List UInt8} (h : (l.all fun c => c != 0x0A) = true) :
    ∀ c ∈ l, c ≠ 0x0A := fun c hc => by simpa using List.all_eq_true.1 h c hc

/-- The line D is found behind the four lines with free numbers. -/
theorem polWord_D (v : VerifierAndGoals.FreeLines) : polWord (VerifierAndGoals.policyFile v) "D" = some 2048 := by
  obtain ⟨U, e⟩ := rest_bytes v
  rw [polWord_policy, e, linesOf_append wholeA1, findWord_append_miss "D" _ _ missA1_D,
    linesOf_valLine (noFeed_of (by rw [bytes_eps1_lo]; decide)),
    findWord_miss _ (missB_head bytes_D bytes_eps1_lo (by decide) (by decide) _),
    linesOf_valLine (noFeed_of (by rw [bytes_eps1_hi]; decide)),
    findWord_miss _ (missB_head bytes_D bytes_eps1_hi (by decide) (by decide) _),
    linesOf_valLine (noFeed_of (by rw [bytes_eps2_lo]; decide)),
    findWord_miss _ (missB_head bytes_D bytes_eps2_lo (by decide) (by decide) _),
    linesOf_valLine (noFeed_of (by rw [bytes_eps2_hi]; decide)),
    findWord_miss _ (missB_head bytes_D bytes_eps2_hi (by decide) (by decide) _),
    linesOf_append wholeA2]
  exact findWord_append_some "D" _ _ 2048 atA2_D

/-! ## 3. The scan's record -/

/-- Where the strict scan returns on the parameter file at v, its record has the eleven numbers. -/
theorem scan_sizes {v : VerifierAndGoals.FreeLines} {P : PolScan}
    (h : polScan (VerifierAndGoals.policyFile v) = .ok P) :
    P.h.prof = 4 ∧ P.h.L = 48 ∧ P.h.d = 5120 ∧ P.h.H = 40 ∧ P.h.Gk = 8 ∧ P.h.dh = 128 ∧
      P.h.f = 16384 ∧ P.h.fe = 8192 ∧ P.h.NE = 128 ∧ P.h.V = 202048 ∧ P.h.D = 2048 := by
  have val : ∀ {n : String} {x : ℕ}, (∀ prof, n ∈ valueNames prof) →
      polWord (VerifierAndGoals.policyFile v) n = some x → P.value n = x := fun hn hx =>
    Option.some.inj ((ConfigReaders.polWord_of_name h hn).symm.trans hx)
  have a0 := val (n := "prof") (by simp [valueNames]) (polWord_A1 v atA1_prof)
  have a1 := val (n := "L") (by simp [valueNames]) (polWord_A1 v atA1_L)
  have a2 := val (n := "d") (by simp [valueNames]) (polWord_A1 v atA1_d)
  have a3 := val (n := "H") (by simp [valueNames]) (polWord_A1 v atA1_H)
  have a4 := val (n := "G") (by simp [valueNames]) (polWord_A1 v atA1_G)
  have a5 := val (n := "dh") (by simp [valueNames]) (polWord_A1 v atA1_dh)
  have a6 := val (n := "f") (by simp [valueNames]) (polWord_A1 v atA1_f)
  have a7 := val (n := "fe") (by simp [valueNames]) (polWord_A1 v atA1_fe)
  have a8 := val (n := "NE") (by simp [valueNames]) (polWord_A1 v atA1_NE)
  have a9 := val (n := "V") (by simp [valueNames]) (polWord_A1 v atA1_V)
  have aD := val (n := "D") (by simp [valueNames]) (polWord_D v)
  rw [ConfigReaders.polScan_h h]
  refine ⟨?_, a1, a2, a3, a4, a5, a6, a7, a8, a9, aD⟩
  show P.value "prof" % 16 = 4
  rw [a0]

/-- The frame's lines of that scan are the written lines. -/
theorem scan_frame {v : VerifierAndGoals.FreeLines} {P : PolScan}
    (h : polScan (VerifierAndGoals.policyFile v) = .ok P) : P.frame = recordLines := by
  obtain ⟨frame, rest, _, _, hr, hf, _⟩ := ConfigReaders.polScan_parts h
  rw [policy_eq, readLines_policy] at hr
  rw [hf]
  exact (congrArg Prod.fst (Except.ok.inj hr)).symm

/-! ## 4. The program's steps from the scan to what the proof of the ranges looks up -/

/-- The layout of a layer sub-proof keeps its shape and has H dh and G dh as the two widths. -/
theorem layout_sizes {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layout h pc = .ok y) : y.h = h ∧ y.dq = h.H * h.dh ∧ y.dkv = h.Gk * h.dh := by
  unfold Layer.layout at e
  obtain ⟨y0, e0, e⟩ := exc_bind e
  have a : y.h = y0.h ∧ y.dq = y0.dq ∧ y.dkv = y0.dkv := by
    unfold Layer.layoutLook at e
    repeat' first
      | (obtain ⟨_, _, e⟩ := exc_bind e)
      | (cases e; exact ⟨rfl, rfl, rfl⟩)
  have b : y0.h = h ∧ y0.dq = h.H * h.dh ∧ y0.dkv = h.Gk * h.dh := by
    unfold Layer.layoutBase at e0
    repeat' first
      | (obtain ⟨_, _, e0⟩ := exc_bind e0)
      | (cases e0; exact ⟨rfl, rfl, rfl⟩)
  exact ⟨a.1.trans b.1, a.2.1.trans b.2.1, a.2.2.trans b.2.2⟩

/-- The layout in what polLayout returns. -/
theorem polLayout_layout {pol : ByteArray} {P : PolScan} {y : Layer.Lay}
    (h : polLayout pol = .ok (P, y)) : Layer.layout (layerShape P) P.polCalls = .ok y := by
  unfold polLayout at h
  obtain ⟨P0, h0, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨y0, hy, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  exact hy

/-- What the layer sub-proofs read holds the layout of the committed matrix that it was given. -/
theorem pubOf_wsLay {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {ws : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {layers : Layer.Pub}
    (h : Layer.Pub.of y sc rope ws V tokv set = .ok layers) : layers.wsLay = ws := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  rfl

/-- The layout of the committed matrix in the public part is made from the scan and the layers'
layout. -/
theorem publicOf_wsLay {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf pol KL layout = .ok X) :
    ∃ y, polLayout pol = .ok (X.P, y) ∧
      wsLayOf (weightShape X.P y) y.h.p3 X.P.lkW = .ok X.layers.wsLay := by
  unfold publicOf at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨sc, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  have h := Fo.Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨ws, hws, h⟩ := exc_bind h
  obtain ⟨rope, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨HLy, _, h⟩ := exc_bind h
  have key : ∃ layers, Layer.Pub.of y sc rope ws P.h.V #[] P.settings = .ok layers ∧
      X.P = P ∧ X.layers = layers := by
    split at h
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨layers, hlay, h⟩ := exc_bind h
      refine ⟨layers, hlay, ?_⟩
      repeat' first
        | (obtain ⟨_, _, h⟩ := exc_bind h)
        | (cases h; exact ⟨rfl, rfl⟩)
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨layers, hlay, h⟩ := exc_bind h
      refine ⟨layers, hlay, ?_⟩
      repeat' first
        | (obtain ⟨_, _, h⟩ := exc_bind h)
        | (cases h; exact ⟨rfl, rfl⟩)
  obtain ⟨layers, hlay, e1, e2⟩ := key
  rw [e1, e2, pubOf_wsLay hlay]
  exact ⟨y, h0, hws⟩

/-- What the key's proof of the ranges looks up, in the shapes that the planner is handed. -/
theorem shapesWith_ranges {X : Public} {links : List Params.ReqLink} {layout : Params.ReqLayout}
    {ids : List Nat} {s : Params.Shapes} (h : shapesWith X links layout ids = .ok s) :
    Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some s.ranges := by
  unfold shapesWith at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := exc_bind h
  have h := Fo.Pub.ite_unit_ok h
  have h := Fo.Pub.ite_unit_ok h
  obtain ⟨r, hr, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  exact Params.orRefuse_ok hr

/-- The same from shapesOf. -/
theorem shapesOf_ranges {X : Public} {lay : Option ByteArray} {links : Array Stages.LinkH}
    {shapes : Params.Shapes} (h : shapesOf X lay = .ok (links, shapes)) :
    Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some shapes.ranges := by
  unfold shapesOf at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨links', declared⟩, _, h⟩ := exc_bind h
  dsimp only at h
  split at h
  · obtain ⟨file, _, h⟩ := exc_bind h
    split at h
    · obtain ⟨⟨reqLinks, layout⟩, _, h⟩ := exc_bind h
      dsimp only at h
      obtain ⟨s, hs, h⟩ := exc_bind h
      have e : (links', s) = (links, shapes) := Except.ok.inj h
      rw [← (Prod.mk.inj e).2]
      exact shapesWith_ranges hs
    · obtain ⟨_, e, _⟩ := exc_bind h
      cases e
  · obtain ⟨_, e, _⟩ := exc_bind h
    cases e

/-! ## 5. The key's sizes at the parameter file at free numbers, and at the scope -/

/-- **At the parameter file at any values of the eight free numbers, any scale file and any layout
file**: the key's sizes in what the program computes are what the sizing returns at the written 32
lines and the layout of the ten written sizes. -/
theorem key_at_policy {v : VerifierAndGoals.FreeLines} {KL : ByteArray} {layout : Option ByteArray}
    {p : Planned} (hp : planned (VerifierAndGoals.policyFile v) KL layout = .ok p) :
    ∃ Y sh, wsLayOf wsFull true recordLines.blockLog = .ok Y ∧
      Plan.shapeOfLayout Y Y.lk = some sh ∧
      Plan.keySized recordLines sh = some p.chains.made.sized.key := by
  obtain ⟨links, shapes, _, _, _, _, _, hX, _, hs, _, _, hc, _, _, _, _⟩ := planned_parts hp
  obtain ⟨y, hy, hw⟩ := publicOf_wsLay hX
  have hS := polLayout_scan hy
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bD⟩ := scan_sizes hS
  have hf := scan_frame hS
  obtain ⟨c1, c2, c3⟩ := layout_sizes (polLayout_layout hy)
  have hq : y.dq = 5120 := by
    rw [c2]
    show p.X.P.h.H * p.X.P.h.dh = 5120
    rw [b3, b5]
  have hkv : y.dkv = 1024 := by
    rw [c3]
    show p.X.P.h.Gk * p.X.P.h.dh = 1024
    rw [b4, b5]
  have h3 : y.h.p3 = true := by
    rw [c1]
    show (p.X.P.h.prof == 3 || (p.X.P.h.prof == 4 && decide (0 < p.X.P.h.NE))) = true
    rw [b0, b8]
    rfl
  have hws : weightShape p.X.P y = wsFull := by
    unfold weightShape wsFull
    simp only [bD, b1, b2, b5, hkv, hq, b6, b7, b8, b9]
  have hlk : p.X.P.lkW = recordLines.blockLog := by
    show p.X.P.frame.blockLog = _
    rw [hf]
  rw [hws, h3, hlk] at hw
  have hk := Params.sized_key (Params.configure_plans hc).1
  rw [hf] at hk
  exact ⟨_, _, hw, shapesOf_ranges hs, hk⟩

/-- What the scope says of the parameter file. -/
theorem inScope_policy {Z : VerifierAndGoals.PublicFiles} (h : VerifierAndGoals.InScope Z = true) :
    ∃ v, Z.pol = VerifierAndGoals.policyFile v := by
  unfold VerifierAndGoals.InScope at h
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  split at h2
  · rw [Bool.and_eq_true] at h2
    exact ⟨_, of_decide_eq_true h2.1⟩
  · cases h2

/-- **At every three public files in the goals' scope.** -/
theorem key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∃ Y sh, wsLayOf wsFull true recordLines.blockLog = .ok Y ∧
      Plan.shapeOfLayout Y Y.lk = some sh ∧
      Plan.keySized recordLines sh = some p.chains.made.sized.key := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hp
  exact key_at_policy hp

/-- **The computed plan's lookups at the key file are the written ones, at every file in scope**:
the records of the two lookups are pubFull₁ and pubFull₂, in this order, at the matrix that the
blocks of a chain take and at the sizing's own; the lookups of the item "ranges" are lk0Full and
lk1Full; both matrices have 2 ^ 18 columns; the oracle message with the multiplicities is number 1.
-/
theorem pubs_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    (Wf.lookupsOf p.chains.made.sized.key.ranges.x
        (Wf.matrixOf p.chains.made.sized.key.once.shape)).map pubOf = [pubFull₁, pubFull₂] ∧
      (Wf.lookupsOf p.chains.made.sized.key.ranges.x p.chains.made.sized.key.ranges.matrix).map
        pubOf = [pubFull₁, pubFull₂] ∧
      p.chains.made.sized.key.ranges.x.lookups = [Johnson.Pack.lk0Full, Johnson.Pack.lk1Full] ∧
      (Wf.matrixOf p.chains.made.sized.key.once.shape).kCol = 18 ∧
      p.chains.made.sized.key.ranges.matrix.kCol = 18 ∧
      p.chains.made.sized.key.ranges.x.messageId = 1 := by
  obtain ⟨Y, sh, hY, hs, hz⟩ := key_at_scope hZ hp
  exact pubs_full hY hs hz

end Lk6.AtPlan

#print axioms Lk6.AtPlan.polWord_D
#print axioms Lk6.AtPlan.scan_sizes
#print axioms Lk6.AtPlan.scan_frame
#print axioms Lk6.AtPlan.layout_sizes
#print axioms Lk6.AtPlan.publicOf_wsLay
#print axioms Lk6.AtPlan.shapesOf_ranges
#print axioms Lk6.AtPlan.key_at_policy
#print axioms Lk6.AtPlan.key_at_scope
#print axioms Lk6.AtPlan.pubs_at_scope
