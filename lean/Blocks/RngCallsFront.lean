-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngCallsFront.lean: the tracking data of the range reduction by calls.

The reduction: Blocks/RngCalls.lean. This file says how it sends its vectors and where the exposed
entries (those that forms may read) come from (tracking data, Blocks/StageTrack.lean); 2 ≠ 0 in E is
assumed throughout the file.
 * `k1` .. `kM`, `trackC`: the tracking data of each step and of the whole protocol
   (Blocks/RngCalls.lean: `Par.core`); `trackC_ok`.
 * `all_trackC`: the reduction sends five vectors: η, η⁰, bit, RA, η¹; no other round has a vector.

Notation: `Q C rows mrow role q`: a property of a vector's code, number of rows, number of row
variables, role and number of positions read: so `G.Cη 1 0 Role.pad G.qη` is η with 1 row and 0 row
variables; `Role` (Blocks/Basic.lean): tested, promised or pad.
Limits: the reduction ends in one linear claim and one index claim (`out`, Blocks/RngCalls.lean). No
declaration of this library takes up `out`: the reduction is composed with no protocol for these two
claims.

Terms: lean/GLOSSARY.md.
-/
import Blocks.RngCallsProps
import Blocks.RngFront
import Blocks.VecEnum
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.RngC.Par

open Iop Prob Finset Alg
open Blocks.Rng (Plan pre pick)
open scoped ENNReal

variable {F : Type} [Field F] [DecidableEq F] (G : Par F) (E : Type) [Field E] [NeZero (2 : E)]
  [Fintype E] [DecidableEq E] [Algebra F E] (pl : G.Places E)

/-- what is exposed from step 3 until RA is sent: the entries of η, η⁰ and bit, and the matrix -/
def rdY1 (X I : Type) : Reads F E ⟨X, G.Y1 E, I⟩ := ⟨G.N1, G.proj1 E, fun y => y.1.1.1⟩

/-- what is exposed from RA to step 10: also the entries of RA -/
def rdY (X I : Type) : Reads F E ⟨X, G.Y E, I⟩ := ⟨G.N, G.proj E, fun y => y.1.1.1.1⟩

instance (X I : Type) : Fintype (G.rdY E X I).N := inferInstanceAs (Fintype G.N)

/-- while the calls run -/
abbrev rdL1 : Reads F E (G.sL1 E) := G.rdY1 E (XL G.N1 E) (IL F E)
abbrev rdL : Reads F E (G.sL E) := G.rdY E (XL G.N E) (IL F E)

/-- What is exposed at the end: also the entries of η¹. -/
def rdsEnd : Reads F E (G.sEnd E pl) := ⟨G.Nend, G.rdEnd E, fun y => y.1.1.1.1.1⟩

instance : Fintype (G.rdsEnd E pl).N := inferInstanceAs (Fintype G.Nend)

/-! ## The tracking data -/

def k1 : (G.co1 E).Track (rd0 (F := F) E) (G.rd1 E) :=
  Core.trackPads G.Cη G.qη G.iη (rd0 (F := F) E)
def k2 : (G.co2 E).Track (G.rd1 E) (G.rd2 E) := Core.trackPads G.C0 G.q0 G.i0 (G.rd1 E)
def k3 : (G.co3 E).Track (G.rd2 E) (G.rdY1 E Unit (Mat F)) :=
  Core.trackNameVec (P := G.P0) (a := G.s2 E) (G.eBit E) (fun e => e.elim) (G.msgBit E) (G.rd2 E)
def k4 : (G.co4 E).Track (G.rdY1 E Unit (Mat F)) (G.rdL1 E) :=
  Core.trackPure (P := G.P0) (a := G.s3 E) (b := G.sL1 E)
    (fun _ => some ⟨Ledger.empty, fun _ => LkX.init Ledger.empty 0, fun _ => 0⟩) id
    (fun W => ⟨W, ⟨0, [], []⟩, G.initA E W⟩) (G.rdY1 E Unit (Mat F)) (G.rdL1 E) id

def k14 (f : ℕ) : (G.co14 E pl f).Track (G.rdL1 E) (G.rdL1 E) :=
  ((G.L1 E pl f).tk14 F (G.rdY1 E (Ledger G.N1 E) (LkA E))).on (a' := G.sL1 E) (b' := G.sL1 E)
    (fun x => x.led) (fun x xo => x.put f xo) id (fun y _ => y) (fun s => s.get f)
    (fun s so => s.put f so) (G.rdL1 E) (G.rdL1 E) id Sum.inl

def k5 (f : ℕ) : (G.co5 E pl f).Track (G.rdL1 E) (G.rdL1 E) :=
  ((G.L1 E pl f).tk5 F (G.rdY1 E (LkX G.N1 E) (LkA E))).on (a' := G.sL1 E) (b' := G.sL1 E)
    (fun x => x.get f) (fun x xo => x.put f xo) id (fun y _ => y) (fun s => s.get f)
    (fun s so => s.put f so) (G.rdL1 E) (G.rdL1 E) id Sum.inl

def k6 (f : ℕ) : (G.co6 E pl f).Track (G.rdL E) (G.rdL E) :=
  ((G.L E pl f).tk6r (G.ru E f) (G.rv E f) F (G.rdY E (LkX G.N E) (LkA E))).on (a' := G.sL E)
    (b' := G.sL E) (fun x => x.get f) (fun x xo => x.put f xo) id (fun y _ => y) (fun s => s.get f)
    (fun s so => s.put f so) (G.rdL E) (G.rdL E) id Sum.inl

/-- the statement types between the message of the masked scalars s_f and the step that stores
them -/
abbrev sSc : Sorts := ⟨XL G.N1 E × (Fin G.plan.nc → E), G.Y1 E, IL F E⟩

def kSc1 :
    (Core.nameScalars (E := E) (G.sL1 E) (fun f : Fin G.plan.nc => pl.cr f) (G.valS E)).Track
      (G.rdL1 E) (G.rdY1 E (G.sSc E).X (G.sSc E).I) :=
  Core.trackNameScalars (a := G.sL1 E) (fun f : Fin G.plan.nc => pl.cr f) (G.valS E) (G.rdL1 E)

def kSc2 :
    (Core.pure (P := G.P0) (E := E) (a := G.sSc E) (b := G.sL1 E)
        (fun o => some { o.1 with s := nat o.2 }) id id).Track
      (G.rdY1 E (G.sSc E).X (G.sSc E).I) (G.rdL1 E) :=
  Core.trackPure (P := G.P0) (a := G.sSc E) (b := G.sL1 E) (fun o => some { o.1 with s := nat o.2 })
    id id (G.rdY1 E (G.sSc E).X (G.sSc E).I) (G.rdL1 E) id

def kSc : (G.coSc E pl).Track (G.rdL1 E) (G.rdL1 E) := (G.kSc1 E pl).seq (G.kSc2 E)

/-- RA is sent; its entries are exposed -/
def kRA : (G.coRA E).Track (G.rdL1 E) (G.rdY E (G.sLa E).X (G.sLa E).I) :=
  Core.trackNameVec (P := G.P0) (a := G.sL1 E) (G.eRA E) (fun e => e.elim) (G.msgRA E) (G.rdL1 E)

def kUp : (G.coUp E).Track (G.rdY E (G.sLa E).X (G.sLa E).I) (G.rdL E) :=
  Core.trackPure (P := G.P0) (a := G.sLa E) (b := G.sL E) (fun x => some (x.push Sum.inl)) id id
    (G.rdY E (G.sLa E).X (G.sLa E).I) (G.rdL E) id

def k7 : (G.co7 E pl).Track (G.rdL E) (G.rdY E (G.s5 E).X (G.s5 E).I) :=
  Core.trackPure (P := G.P0) (a := G.sL E) (b := G.s5 E)
    (fun x => some (x.led.addLins (G.lins E pl x), (fun f => (x.c f).z, x.s))) id
    (fun s => (s.hl.toClose (G.nR E) (G.nO E), (s.W, fun f => (s.a f).z))) (G.rdL E)
    (G.rdY E (G.s5 E).X (G.s5 E).I) id

def k8 :
    (G.co8 E pl).Track (G.rdY E (G.s5 E).X (G.s5 E).I) (G.rdY E (G.s6 E).X (G.s6 E).I) :=
  (Closing.track (E := E) (G.nL E) (G.plN E pl) pl.cl F).on (a' := G.s5 E) (b' := G.s6 E)
    (fun x => x.1) (fun x g => (g, x.2)) (G.proj E) (fun y _ => y) (fun s => s.1)
    (fun s so => (so, s.2)) (G.rdY E (G.s5 E).X (G.s5 E).I)
    (G.rdY E (G.s6 E).X (G.s6 E).I) id Sum.inl

/-- steps 1 to 10 -/
def kA : (G.coA E pl).Track (rd0 (F := F) E) (G.rdY E (G.s6 E).X (G.s6 E).I) :=
  (G.k1 E).seq
    ((G.k2 E).seq
      ((G.k3 E).seq
        ((G.k4 E).seq
          ((Core.Track.rep (G.k14 E pl) G.plan.nc 0).seq
            ((Core.Track.rep (G.k5 E pl) G.plan.nc 0).seq
              ((G.kSc E pl).seq
                ((G.kRA E).seq
                  ((G.kUp E).seq
                    ((Core.Track.rep (G.k6 E pl) G.plan.nc 0).seq
                      ((G.k7 E pl).seq (G.k8 E pl)))))))))))

def kM : (G.coM E pl).Track (G.rdY E (G.s6 E).X (G.s6 E).I) (G.rdsEnd E pl) :=
  ((G.M E pl).trackPadsMerge G.C1 (Fin G.plan.nc) G.q1 Sum.inr
      G.vars ⟨G.N, G.proj E, fun y => y.1.1.1.1⟩).on
    (a' := G.s6 E) (b' := G.sEnd E pl) (fun x j => G.idxOf E pl x.2 j)
    (fun x a => (Form.push Sum.inl x.1, a)) id (fun y yo => (y, yo.2))
    (fun s => (fun j => G.gpsi E s.2.2 j, fun q c => algebraMap F E (s.2.1 q.val (num c))))
    (fun _ so => so) (G.rdY E (G.s6 E).X (G.s6 E).I) (G.rdsEnd E pl) id
    fun n => n.elim Sum.inl fun j => Sum.inr (Sum.inr j)

/-- How the reduction sends its vectors, and where the exposed entries come from. -/
def trackC : (G.core E pl).Track (rd0 (F := F) E) (G.rdsEnd E pl) :=
  ((G.kA E pl).mapP Sum.inl).seq (G.kM E pl)

/-- `trackC`, stated for the stage -/
def track : (G.stage E pl).Track (rd0 (F := F) E) (G.rdsEnd E pl) := G.trackC E pl

theorem k14_ok (f : ℕ) : (G.k14 E pl f).OK :=
  ((G.L1 E pl f).track14_ok F _).on _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ _ => rfl) fun _ _ => rfl
theorem k5_ok (f : ℕ) : (G.k5 E pl f).OK :=
  ((G.L1 E pl f).track5_ok F _).on _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ _ => rfl) fun _ _ => rfl
theorem k6_ok (f : ℕ) : (G.k6 E pl f).OK :=
  ((G.L E pl f).track6r_ok (G.ru E f) (G.rv E f) F _).on _ _ _ _ _ _ (fun _ _ => rfl)
    (fun _ _ _ => rfl) fun _ _ => rfl

theorem kSc_ok : (G.kSc E pl).OK :=
  Core.Track.OK.seq (t₁ := G.kSc1 E pl) (t₂ := G.kSc2 E)
    (Stage.trackNameScalars_ok
      (a := G.sL1 E) (fun f : Fin G.plan.nc => pl.cr f) (G.valS E) (G.rdL1 E))
    (Stage.trackPure_ok (P := G.P0) (a := G.sSc E) (b := G.sL1 E) _ _ _ _ _ _
      (fun _ _ => rfl) fun _ => rfl)

theorem kA_ok : (G.kA E pl).OK :=
  Core.Track.OK.seq (Stage.trackPads_ok G.Cη G.qη _ _) <|
  Core.Track.OK.seq (Stage.trackPads_ok G.C0 G.q0 _ _) <|
  Core.Track.OK.seq (Stage.trackNameVec_ok
    (P := G.P0) (a := G.s2 E) (G.eBit E) (fun e => e.elim) (G.msgBit E) (G.rd2 E)) <|
  Core.Track.OK.seq (Stage.trackPure_ok _ _ _ _ _ _ (fun _ _ => rfl) fun _ => rfl) <|
  Core.Track.OK.seq (Core.Track.OK.rep (G.k14_ok E pl) _ _) <|
  Core.Track.OK.seq (Core.Track.OK.rep (G.k5_ok E pl) _ _) <|
  Core.Track.OK.seq (G.kSc_ok E pl) <|
  Core.Track.OK.seq (Stage.trackNameVec_ok
    (P := G.P0) (a := G.sL1 E) (G.eRA E) (fun e => e.elim) (G.msgRA E) (G.rdL1 E)) <|
  Core.Track.OK.seq (t₁ := G.kUp E)
      (Stage.trackPure_ok (P := G.P0) (a := G.sLa E) (b := G.sL E) _ _ _ _ _ _
        (fun _ _ => rfl) fun _ => rfl) <|
  Core.Track.OK.seq (Core.Track.OK.rep (G.k6_ok E pl) _ _) <|
  Core.Track.OK.seq (Stage.trackPure_ok _ _ _ _ _ _ (fun _ _ => rfl) fun _ => rfl)
    ((Closing.track_ok (E := E) (G.nL E) (G.plN E pl) pl.cl F).on _ _ _ _ _ _ (fun _ _ => rfl)
      (fun _ _ _ => rfl) fun _ _ => rfl)

theorem kM_ok : (G.kM E pl).OK := by
  refine Core.Track.OK.on
    ((G.M E pl).trackPadsMerge_ok
      G.C1 (Fin G.plan.nc) G.q1 Sum.inr G.vars ⟨G.N, G.proj E, fun y => y.1.1.1.1⟩)
    _ _ _ _ _ _ (fun _ _ => rfl) (fun y yo n => ?_) fun _ _ => rfl
  rcases n with m | j <;> rfl

theorem trackC_ok : (G.trackC E pl).OK := ((G.kA_ok E pl).mapP Sum.inl).seq (G.kM_ok E pl)

/-! ## Five vectors -/

section Four

variable {E pl}

/-- A property Q that η, η⁰, bit, RA and η¹ have holds of all vectors of the reduction. -/
theorem all_trackC {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} (hη : Q G.Cη 1 0 Role.pad G.qη)
    (h0 : Q G.C0 1 0 Role.pad G.q0) (hb : Q G.Cb G.rowsB G.mrowB Role.tested G.qb)
    (hA : Q G.CA G.rowsA G.mrowA Role.tested G.qA) (h1 : Q G.C1 1 0 Role.pad G.q1) :
    (G.trackC E pl).All Q :=
  Core.Track.All.seq (t₁ := (G.kA E pl).mapP Sum.inl) (t₂ := G.kM E pl)
    (Core.Track.All.mapP (t := G.kA E pl)
      (Core.Track.All.seq (t₁ := G.k1 E) ⟨fun _ => hη, trivial⟩ <|
        Core.Track.All.seq (t₁ := G.k2 E) ⟨fun _ => h0, trivial⟩ <|
        Core.Track.All.seq (t₁ := G.k3 E) ⟨fun _ => hb, trivial⟩ <|
        Core.Track.All.seq (t₁ := G.k4 E) trivial <|
        Core.Track.All.seq (t₁ := Core.Track.rep (G.k14 E pl) G.plan.nc 0)
          (Core.Track.All.rep (t := G.k14 E pl)
            (fun f => (G.L1 E pl f).all_track14 (G.rdY1 E (Ledger G.N1 E) (LkA E))) _ _) <|
        Core.Track.All.seq (t₁ := Core.Track.rep (G.k5 E pl) G.plan.nc 0)
          (Core.Track.All.rep (t := G.k5 E pl)
            (fun f => (G.L1 E pl f).all_track5 (G.rdY1 E (LkX G.N1 E) (LkA E))) _ _) <|
        Core.Track.All.seq (t₁ := G.kSc E pl)
          (Core.Track.All.seq (t₁ := G.kSc1 E pl) (t₂ := G.kSc2 E)
            ⟨fun e : Empty => e.elim, trivial⟩ trivial) <|
        Core.Track.All.seq (t₁ := G.kRA E) ⟨fun _ => hA, trivial⟩ <|
        Core.Track.All.seq (t₁ := G.kUp E) trivial <|
        Core.Track.All.seq (t₁ := Core.Track.rep (G.k6 E pl) G.plan.nc 0)
          (Core.Track.All.rep (t := G.k6 E pl)
            (fun f => (G.L E pl f).all_track6r (G.ru E f) (G.rv E f) (G.rdY E (LkX G.N E) (LkA E)))
            _ _) <|
        Core.Track.All.seq (t₁ := G.k7 E pl) (t₂ := G.k8 E pl) trivial
          (Rng.all_closing (F := F) (E := E) (G.nL E) (G.plN E pl) pl.cl)) Sum.inl)
    ((G.M E pl).all_trackPadsMerge G.C1 (Fin G.plan.nc) G.q1 Sum.inr G.vars _ h1)

end Four

end Blocks.RngC.Par

