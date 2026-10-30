-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Holes/HoleC.lean.
The knowledge soundness of a sub-proof's lookup, as closed statements with their proofs.

Each statement is a definition of a proposition in which every letter is bound, and a theorem
without binders proves it. The form is `KnowAt` (Cb/G6/Cut.lean): the shape is of the point kind,
the reduction is local, the condition behind the block holds of every output on an input that meets
the condition before it, and, for each fixed tuple of committed messages, knowledge soundness.

 * `HC`: for every finite field E of characteristic p, every caller's state, every record `A0` of
   the one lookup's numbers, places, orders and padding, every forest of calls `h`
   (`OnBytes.Model.Forest.Shape`), all tables `T` and key vectors `K`, all short sumcheck blocks
   `V`, `VC` (records `TWhole.ShortK`, `TWhole.ShortKC`, which hold the block's own knowledge
   soundness as a field: whoever uses `HC` hands in such a pair), every joint `R0` and reading
   `msg` of the committed messages: under seven conditions on public numbers (`Port.OK h`; at most
   p calls; h.v = A0.v' + 1; h.d = A0.d; `Adm p` of Cb/Ld/LdLkp.lean on the sizes; `padsOK`; all
   planes of bits count: A0.n + 2 = 2 ^ A0.w),
   `KnowAt` of the reduction "theta's draw if there are several calls, then the whole lookup at the
     shifted vectors"
   from the joint "R0, and each call's keys lie in that call's table"
   to the joint "R0 at the caller's state, and the claim on the shifted joint keys and all rows
     that the block hands on hold",
   with the identity on the further witness as extractor, at the block's own errors.
 * `HCgen`: the same for any maps from joint indices to calls, with the draw or without it
   (`several`); `P.Ok several` stands in place of the first two conditions.
 * `HShift`: the draw of theta alone, for any maps, under `P.Tags`, at the count 2 ^ P.d.
 * `HCsig`: `HC`'s block over a signature, whose messages are then the committed messages; by the
   rule `sigLift_know` (Cb/Ld/LdSigLift.lean). Its form is `Know` alone, not `KnowAt`; the
   extractor is the identity.
 * `hC`, `hCgen`, `hShift`, `hCsig`: the proofs.

Not claimed here: that `A0` holds what belongs to `h` (its fields St, key, tab are not read); that
`T` and `K` are a sub-proof's tables and keys; that the maps of `Port.Q` are those by which the
verifier under OnBytes/ reads a forest, or that every forest that it builds meets `Port.OK` (see the
head of OnBytes/Tie/Pv/Lookup/Port/ShiftQPort.lean); that the claims behind the block are the values
that the program's verifier computes; anything about an honest prover; what the short sumcheck
blocks put out (a block that refuses everything is among them: the statement at the named blocks is
in OnBytes/Tie/Pv/Lookup/Holes/HoleC0.lean).

-/
import OnBytes.Tie.Pv.Lookup.Shift.ShiftK

set_option autoImplicit false

namespace Cb.Fo
open Finset Prob Cb.Lkp Cb.LdLkp Cb.LdLkp.Kn Iop IOR TWhole

/-- The shift: one draw θ, from "each key is a row of its own call" to "each shifted key is a row of
the shifted joint table", under `P.Tags`, at the count 2 ^ P.d. -/
def HShift : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (St J M Wp Kc : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E))
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E),
    P.Tags →
    KnowAt (P.bkK Ex).R ((P.on msg).jIn R0) ((P.on msg).jOut R0) (fun _ _ _ wp => wp) (P.bkK Ex).e

/-- A lookup of one or several calls, for any maps from joint indices to calls. -/
def HCgen : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E)
    (P : ShiftQ E St (A0.J → E)) (several : Bool)
    (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → A0.J → E),
    P.Ok several → P.v = A0.v' + 1 → P.d = A0.d → A0.H.lkb.Adm p →
    padsOK (A0.v' + 1) A0.d A0.pads = true → A0.n + 1 + 1 = 2 ^ A0.w →
    KnowAt (P.allK A0 several V VC (Ex := Ex)).R
      ((P.on msg).jIn R0)
      (cj (ShiftQ.ride R0) msg Prod.fst ((P.asmH A0).lk.out id id) ((P.asmH A0).lk.out id id))
      (fun _ _ _ wp => wp) (P.allK A0 several V VC (Ex := Ex)).e

/-- A sub-proof's lookup, on the record of a forest of calls. -/
def HC : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E)
    (h : OnBytes.Model.Forest.Shape) (T : St → ℕ → ℕ → E) (K : St → (A0.J → E) → ℕ → ℕ → E)
    (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → A0.J → E),
    Port.OK h → h.NC ≤ p → h.v = A0.v' + 1 → h.d = A0.d → A0.H.lkb.Adm p →
    padsOK (A0.v' + 1) A0.d A0.pads = true → A0.n + 1 + 1 = 2 ^ A0.w →
    KnowAt ((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := Ex)).R
      (Port.jIn h T K msg R0)
      (cj (ShiftQ.ride R0) msg Prod.fst (((Port.Q h T K).asmH A0).lk.out id id)
        (((Port.Q h T K).asmH A0).lk.out id id))
      (fun _ _ _ wp => wp) ((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := Ex)).e

/-- The same over a signature: the committed messages are the signature's. -/
def HCsig : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E)
    (h : OnBytes.Model.Forest.Shape) (T : St → ℕ → ℕ → E) (K : St → (A0.J → E) → ℕ → ℕ → E)
    (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Sg : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (R0 : Rels Kc St E₀ (Sg.Msg × Wp))
    (msg : Sg.Msg → A0.J → E),
    Port.OK h → h.NC ≤ p → h.v = A0.v' + 1 → h.d = A0.d → A0.H.lkb.Adm p →
    padsOK (A0.v' + 1) A0.d A0.pads = true → A0.n + 1 + 1 = 2 ^ A0.w →
    (((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := E₀)).R.keep Sg.Smp Sg.ext).red.Know
      (Sg.over (Port.jIn h T K msg R0)).on
      (Sg.over (Port.jIn h T K msg R0)).relR
      (Sg.over (cj (ShiftQ.ride R0) msg Prod.fst (((Port.Q h T K).asmH A0).lk.out id id)
        (((Port.Q h T K).asmH A0).lk.out id id))).relR
      (fun _ _ w => (w.1, w.2)) ((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := E₀)).e

theorem hShift : HShift := fun E _ _ St J M Wp Kc Ex P R0 msg hT =>
  shiftK_knowAt E St J M Wp Kc Ex P R0 msg hT

theorem hCgen : HCgen := fun E _ _ p _ St A0 P several V VC Ex Kc M Wp R0 msg hOk hv hd hA hP hF =>
  allK_base E p St A0 P several V VC Ex Kc M Wp R0 msg hOk hv hd hA hP hF

theorem hC : HC := fun E _ _ p _ St A0 h T K V VC Ex Kc M Wp R0 msg hOK hp hv hd hA hP hF =>
  port_jIn E St A0.J M Kc Wp Ex h T K msg R0 hOK ▸
    hCgen E p St A0 (Port.Q h T K) (Port.several h) V VC Ex Kc M Wp R0 msg
      (port_ok E p St A0.J h T K hOK hp) hv hd hA hP hF

theorem hCsig : HCsig :=
  fun E _ _ p _ St A0 h T K V VC Sg E₀ Kc Wp R0 msg hOK hp hv hd hA hP hF =>
    sigLift_know E Sg Kc _ _ Wp Wp E₀ E₀ ((Port.Q h T K).allK A0 (Port.several h) V VC).R _ _
      (fun _ _ _ wp => wp) ((Port.Q h T K).allK A0 (Port.several h) V VC).e
      (hC E p St A0 h T K V VC E₀ Kc Sg.Msg Wp R0 msg hOK hp hv hd hA hP hF).know

end Cb.Fo
