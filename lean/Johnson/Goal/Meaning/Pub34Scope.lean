-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/Pub34Scope.lean: the public fields of the record Pub34
(Johnson/Road/Rows/LayerEnds34.lean:182 ff.) at all public files in the goals' scope.

Pub34 gathers what the theorems on a layer sub-proof's claims ask. Some of its fields are
letters of a run (not shown here). The fields below speak of the public files alone. Each is shown
here from the three facts of Johnson/Goal/Meaning/ScopeTop.lean: VerifierAndGoals.InScope Z = true,
VerifierAndGoals.readFiles Z = .ok pp, publicOf Z.pol Z.KL lay = .ok X; at the letters h := layerShape X.P,
pc := X.P.polCalls, y := X.y, sc := X.layers.sc, rd := X.layers.rd, D := DF,
s := weightShape X.P X.y, lk := kRef.

Main theorems.
  more_of_public: five more lines of publicOf on its own results: the reads are what readsOf
    returns; the tails are tailsOf; the rotary table is what ropeOf returns; the layers' record is
    what Pub.of returns; the plans are what plansG returns. (That the scales have passed scalesHeld
    is shown: Hd.scalesHeld_of_public, Johnson/Road/HeadL5Grp.lean:187.)
  takeSegments_names, takeCalls_names, place_names, calls_of_base, lines_of_layout: the names in a
    layout's calls are the words of the call lines from the third on.
  linesAre_in_scope (hN) · cap_in_scope (hc) · floor_in_scope (hfl) · scales_in_scope (hs) ·
    more_of_public, first clause (hrd).
  shape_in_scope: layerShape X.P is the hand-written hKF but for eps1, eps2, epsF.
  pub34_public: these, with hy, S, Z, h4, Zw, hsL, hlw, as one statement.
  tails_of_public (htm | hNM) · mats_of_public (hmats): wherever publicOf returns.
Not here: hs0, hpad, R; hg and hρ are letters of a caller.
-/
import Johnson.Goal.Meaning.EmbScope
import Johnson.Road.Rows.LayerEnds34
import Johnson.Road.FormsKeysRunK
import Johnson.Road.FormsKeysPlan

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)

/-! ## Five more lines of publicOf -/

/-- What the layers' public record keeps of its arguments, beside pub_fields. -/
theorem pub_more {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Layer.Pub}
    (hP : Layer.Pub.of y sc rope wsLay V tokv set = .ok P) :
    P.y = y ∧ P.sc = sc ∧ readsOf y = .ok P.rd ∧ P.tails = tailsOf y ∧ P.rope = rope := by
  unfold Layer.Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, hr, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  exact ⟨rfl, rfl, hr, rfl, rfl⟩

/-- Five more lines of the public part, on its own results. -/
theorem more_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) :
    readsOf X.y = .ok X.layers.rd ∧
      X.layers.tails = tailsOf X.y ∧ ropeOf X.y.h = .ok X.layers.rope ∧
      Layer.Pub.of X.y X.layers.sc X.layers.rope X.layers.wsLay X.P.h.V #[] X.P.settings =
        .ok X.layers ∧ Layer.plansG X.layers = .ok X.G := by
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := Hd.ok_of_either h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := Hd.ok_of_either2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  obtain ⟨e1, e2, e3, e4, e5⟩ := pub_more (by assumption)
  obtain ⟨-, e6⟩ := Hd.pub_fields (by assumption)
  unfold Model.Verify.Public.y
  dsimp only
  rw [e1, e2, e4, e5, e6]
  exact ⟨e3, rfl, by assumption, by assumption, by assumption⟩

/-! ## The names in a layout's calls -/

/-- The segments that a line takes have the line's names, in order. -/
theorem takeSegments_names (sd : List (String × String × ℕ × Bool)) (kind : String) :
    ∀ (ns seen : List String) (r : List SegAsk × List String),
      takeSegments sd kind ns seen = .ok r → r.1.map (·.1) = ns
  | [], _, _, h => by
    cases h
    rfl
  | n :: ns, seen, r, h => by
    rw [takeSegments] at h
    cases hf : sd.find? (fun s => s.1 == n) with
    | none =>
      rw [hf] at h
      cases h
    | some s =>
      rw [hf] at h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨r', h1, h2⟩ := ok_of_bind h
      cases h2
      have e : s.1 = n := by simpa using List.find?_some hf
      show s.1 :: r'.1.map (·.1) = n :: ns
      rw [e, takeSegments_names sd kind ns (n :: seen) r' h1]

/-- The calls that the lines give have, call by call, the lines' words from the third on. -/
theorem takeCalls_names (sd : List (String × String × ℕ × Bool)) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List (String × String × List SegAsk) × List String),
      takeCalls sd lines names seen = .ok r →
      r.1.map (fun c => c.2.2.map (·.1)) = lines.map (·.drop 2)
  | [], _, _, _, h => by
    cases h
    rfl
  | ln :: rest, names, seen, r, h => by
    rcases ln with _ | ⟨name, _ | ⟨kind, _ | ⟨s, more⟩⟩⟩
    · cases h
    · cases h
    · cases h
    · have h : (do
          refuseIf (names.contains name) "policy-call-list"
          refuseIf (["V", "a", "b", "E"].contains name) "policy-call-list"
          let a ← takeSegments sd kind (s :: more) seen
          let r ← takeCalls sd rest (name :: names) a.2
          pure ((name, kind, a.1) :: r.1, r.2)) = .ok r := h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨a', h1, h⟩ := ok_of_bind h
      obtain ⟨r', h2, h⟩ := ok_of_bind h
      cases h
      show a'.1.map (·.1) :: r'.1.map (fun c => c.2.2.map (·.1)) =
        (s :: more) :: rest.map (·.drop 2)
      rw [takeSegments_names sd kind (s :: more) seen a' h1,
        takeCalls_names sd rest (name :: names) a'.2 r' h2]

/-- A numbered list, mapped through a function of the members alone. -/
theorem map_zipIdx {α β : Type} (g : α → β) : ∀ (l : List α) (n : ℕ),
    (l.zipIdx n).map (fun x => g x.1) = l.map g
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, map_zipIdx g l]

/-- A placed call's segments have the asks' names, in order. -/
theorem place_names (name kind : String) (asks : List SegAsk) (fl : ℕ) :
    (place name kind asks fl).segs.map (·.name) = asks.map (·.1) := by
  unfold place
  dsimp only
  rw [List.map_map]
  exact map_zipIdx (·.1) asks 0

/-- The first half of the layout places what takeCalls takes from the call lines (from the built-in
lines if there are none). -/
theorem calls_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) :
    ∃ taken, takeCalls (segmentList h (h.H * h.dh + h.Gk * h.dh) (h.Gk * h.dh))
        (if pc.isEmpty then builtInCalls h.p3 else pc) [] [] = .ok taken ∧
      y.calls = (taken.1.map fun c => place c.1 c.2.1 c.2.2 (h.nmin - h.ll - h.lt)).toArray := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, ht, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  exact ⟨taken, ht, rfl⟩

/-- The names in the calls of a layout that the verifier returns on call lines that are there: the
lines' words from the third on. -/
theorem lines_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (hpc : pc.isEmpty = false) :
    y.calls.toList.map (fun cd => cd.segs.map (·.name)) = pc.map (·.drop 2) := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  obtain ⟨taken, ht, hc⟩ := calls_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  show y0.calls.toList.map _ = _
  rw [hpc, if_neg (by decide)] at ht
  rw [hc, ← takeCalls_names _ _ _ _ _ ht, List.map_map]
  exact List.map_congr_left fun c _ => place_names _ _ _ _

/-- The stored example's call lines name the library's families, call by call. -/
theorem callsRef_lines : VerifierAndGoals.Lines.callsRef.map (·.drop 2) =
    (List.finRange 8).map fun cc => (fams cc).map segName := by decide

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- hN. -/
theorem linesAre_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : LinesAre X.y := by
  have B := Hd.publicH_of_public h
  have hc := (Hd.calls_of_scope hZ hR h).1
  have hl := B.lay
  rw [hc] at hl
  unfold LinesAre
  rw [lines_of_layout hl rfl]
  exact callsRef_lines

/-- hc. -/
theorem cap_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : DF.cap = (layerShape X.P).lidb := by
  rw [Hd.scan_of_scope hZ hR h]
  rfl

/-- The library's numbers of columns in use, against 2^8. -/
theorem floor_ref : ∀ k : Fin 8, 20 - 2 - 10 ≤ Nat.clog 2 (used DF k) := by
  intro k
  have h : 2 ^ 7 < used DF k := by
    revert k
    decide +kernel
  exact (Nat.lt_clog_iff_pow_lt (by decide)).mpr h

/-- hfl. -/
theorem floor_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : ∀ k : Fin 8,
    (layerShape X.P).nmin - (layerShape X.P).ll - (layerShape X.P).lt ≤
      Nat.clog 2 (used DF k) := by
  have A := Hd.core_of_scope hZ hR h
  have e1 : (layerShape X.P).ll = 2 := A.num 3
  have e2 : (layerShape X.P).lt = 10 := A.num 1
  have e3 : (layerShape X.P).nmin = 20 := by
    rw [Hd.scan_of_scope hZ hR h]
    rfl
  rw [e1, e2, e3]
  exact floor_ref

/-- hs. -/
theorem scales_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    scalesHeld (layerShape X.P) X.layers.sc = .ok () := by
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.publicH_of_public h
  obtain ⟨eh, -⟩ := laid_of_layout B.lay (Hd.switches_of_core A).p3
  rw [← eh]
  exact Hd.scalesHeld_of_public h

/-- htm | hNM, for the plan of every group: plan_sizes at X's own plans. No premise on
the files but that publicOf returns. -/
theorem tails_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) {g : ℕ} {hp : Layer.HPlan2} (hg : X.G[g]? = some hp) :
    (hp.tl.mats.map fun M => (M.m, M.k)) = matsR X.y g ∧ hp.tl.NM = hp.tl.mats.size := by
  obtain ⟨-, -, -, hP, hG⟩ := more_of_public h
  exact plan_sizes hP hG hg

/-- hmats: the rows and columns of the matrices that the check of group g takes from the public
record are matsR. -/
theorem mats_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (g : ℕ) :
    ((X.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR X.y g := by
  rw [(more_of_public h).2.1]
  rfl

/-- The shape of the closed form of the scan: four fields whose names the record's reader spells by
joining strings, the profile (a remainder), then all others. -/
theorem shape_of_closed (v : VerifierAndGoals.FreeLines) :
    layerShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef v) = { hKF with
      eps1 := (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef v).h.eps.getD 0 0,
      eps2 := (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef v).h.eps.getD 1 0,
      epsF := (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef v).h.epsF } := by
  generalize hS : VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef v = S
  have mm : ∀ {α : Type} (l : List α) (nm : α → String) (get : String → ℕ),
      l.map (fun c => get (nm c)) = (l.map nm).map get := fun l nm get => by
    rw [List.map_map]
    rfl
  have s1 : "theta0" ++ "_lo" = "theta0_lo" := by decide +kernel
  have s2 : "theta0" ++ "_hi" = "theta0_hi" := by decide +kernel
  have s3 : "seed" ++ "_lo" = "seed_lo" := by decide +kernel
  have s4 : "seed" ++ "_hi" = "seed_hi" := by decide +kernel
  have s5 : (["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"].map
      fun k => "wb_" ++ k) = ["wb_qk", "wb_v", "wb_o", "wb_g", "wb_u", "wb_gs", "wb_us", "wb_gr",
        "wb_ur", "wb_dn", "wb_dnr", "wb_r"] := by decide +kernel
  have s6 : ((List.range 8).map fun c => "iota_" ++ toString c) = ["iota_0", "iota_1", "iota_2",
      "iota_3", "iota_4", "iota_5", "iota_6", "iota_7"] := by decide +kernel
  have t0 : (layerShape S).theta0 = 500000 := by
    subst hS
    show (fun n => ((VerifierAndGoals.Lines.valuesAt v).lookup n).getD 0) ("theta0" ++ "_lo") + 2 ^ 32 *
      (fun n => ((VerifierAndGoals.Lines.valuesAt v).lookup n).getD 0) ("theta0" ++ "_hi") = 500000
    rw [s1, s2]
    rfl
  have t1 : (layerShape S).seed = 1 := by
    subst hS
    show (fun n => ((VerifierAndGoals.Lines.valuesAt v).lookup n).getD 0) ("seed" ++ "_lo") + 2 ^ 32 *
      (fun n => ((VerifierAndGoals.Lines.valuesAt v).lookup n).getD 0) ("seed" ++ "_hi") = 1
    rw [s3, s4]
    rfl
  have t2 : (layerShape S).wb = Array.replicate 12 13 := by
    subst hS
    show (["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"].map
      fun k => (fun n => ((VerifierAndGoals.Lines.valuesAt v).lookup n).getD 0) ("wb_" ++ k)).toArray = _
    rw [mm _ (fun k => "wb_" ++ k) (fun n => ((VerifierAndGoals.Lines.valuesAt v).lookup n).getD 0), s5]
    rfl
  have t3 : (layerShape S).iota = #[1, 1, 1, 2, 1, 1, 0, 0] := by
    subst hS
    show ((List.range 8).map fun c =>
      (fun n => ((VerifierAndGoals.Lines.valuesAt v).lookup n).getD 0) ("iota_" ++ toString c)).toArray = _
    rw [mm _ (fun c => "iota_" ++ toString c)
      (fun n => ((VerifierAndGoals.Lines.valuesAt v).lookup n).getD 0), s6]
    rfl
  have t4 : (layerShape S).prof = 4 := by
    subst hS
    have a : ((VerifierAndGoals.Lines.valuesAt v).lookup "prof").getD 0 = 20 := rfl
    show ((VerifierAndGoals.Lines.valuesAt v).lookup "prof").getD 0 % 16 = 4
    rw [a]
  have e0 : layerShape S = { layerShape S with
      theta0 := (layerShape S).theta0, seed := (layerShape S).seed, wb := (layerShape S).wb,
      iota := (layerShape S).iota, prof := (layerShape S).prof } := rfl
  rw [e0, t0, t1, t2, t3, t4]
  subst hS
  rfl

/-- THE PLAN's SHAPE IS THE HAND-WRITTEN hKF (Johnson/Road/FormsKeysRunK.lean:278) but for the three
free numbers eps1, eps2, epsF, which are those that the goals' reader read. -/
theorem shape_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    layerShape X.P = { hKF with
      eps1 := (VerifierAndGoals.freeLinesOf pp).eps1, eps2 := (VerifierAndGoals.freeLinesOf pp).eps2,
      epsF := (VerifierAndGoals.freeLinesOf pp).epsF } := by
  have hX := Hd.scan_of_public h
  rw [Hd.policy_of_scope hZ hR] at hX
  obtain ⟨e1, -, -, e4, -, -, -⟩ := VerifierAndGoals.Lines.hdr_free hX
  have e : layerShape X.P = { hKF with
      eps1 := X.P.h.eps.getD 0 0, eps2 := X.P.h.eps.getD 1 0, epsF := X.P.h.epsF } := by
    rw [Hd.scan_of_scope hZ hR h]
    exact shape_of_closed _
  rw [e, e1, e4]
  rfl

/-- THE PUBLIC FIELDS OF Pub34, at all public files in the goals' scope, in the record's own names:
hy · S · hs · hrd · Z · hc · hN · hfl · Zw · hsL · hlw · h4. -/
theorem pub34_public (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    layout (layerShape X.P) X.P.polCalls = .ok X.y ∧ Switches (layerShape X.P) ∧
      scalesHeld (layerShape X.P) X.layers.sc = .ok () ∧ readsOf X.y = .ok X.layers.rd ∧
      Sized (layerShape X.P) DF ∧ DF.cap = (layerShape X.P).lidb ∧ LinesAre X.y ∧
      (∀ k : Fin 8, (layerShape X.P).nmin - (layerShape X.P).ll - (layerShape X.P).lt ≤
        Nat.clog 2 (used DF k)) ∧
      SizedW (weightShape X.P X.y) DF.P ∧ (weightShape X.P X.y).L = (layerShape X.P).L ∧
      wsLayOf (weightShape X.P X.y) true kRef = .ok X.layers.wsLay ∧
      (layerShape X.P).p4 = true := by
  have A := Hd.core_of_scope hZ hR h
  have H := Hd.public_of_core h A
  obtain ⟨-, S, W, -⟩ := Emb.emb_public_in_scope hZ hR h
  exact ⟨H.lay, H.switches, scales_in_scope hZ hR h, (more_of_public h).1, H.sized,
    cap_in_scope hZ hR h, linesAre_in_scope hZ hR h, floor_in_scope hZ hR h, S, rfl, W, H.p4⟩

#print axioms more_of_public
#print axioms lines_of_layout
#print axioms callsRef_lines
#print axioms linesAre_in_scope
#print axioms cap_in_scope
#print axioms floor_ref
#print axioms floor_in_scope
#print axioms scales_in_scope
#print axioms tails_of_public
#print axioms mats_of_public
#print axioms shape_in_scope
#print axioms pub34_public

end Meaning.P34
