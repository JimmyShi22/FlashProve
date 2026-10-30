-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieBehind.lean: THE TABLE'S
BOOK-KEEPING BEHIND THE KIND'S OWN BLOCK: the table's Bool on the first chain's record (shape₁:
Johnson/Desc/Key/KeyShape.lean, at the filling of Johnson/RunOne/KeyReaders1.lean) steps from border
4 to 5 and from 10 to 11, where the record behind is the record in front with what was heard and a
ledger put, the ledger sized, with as many slots taken as the lookup's face has, and with that room.

Main names:
  t_k3₀, t_k3₁: the ties between plan and record do not read what the block writes.
  c_4_5, c_10_11: the core's step. sh_4_5, sh_10_11: shape₁'s.
  slots₁_eq: the table's number of hidden values of lookup l is the face's.
  on_4_5, on_10_11: the table's whole promise on₁ steps likewise across a piece whose yes puts such
    a ledger, by other files' onAt_fwd, free₁_step and strsStay_of_out.
  samePins_put: the table's reading at the first chain does not read what the block writes.

Object: the table's Bool shape₁; lookupSeat.put (Johnson/Desc/Key/Link.lean).
User: on_behind_k3 (TieBehindK3.lean).
Letters: one, s, g, G.

Limits. The three facts on the ledger are premises here. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieStated
import Johnson.RunOne.KeyTenKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieBehind
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Model (Fork)
open VerifiableInference.Desc.K3
open OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi FirstState Claim lookupSeat lookupsOf sentB groupB doneB core₁
  shape₁ shape₁_step KRead Where pinned SamePins onAt_fwd strsStay_of_out)
open Johnson.RunOne.KeyRows23 (BaseSt)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁ ties₁ open₁ on₁ on₁_two free₁_step
  CollCell)
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK

variable (one : OneTime) (s : FirstState) (g : HeardG) (G : Fork)

theorem t_k3₀ : ties₁ one 5 (lookupSeat.put s g G) = ties₁ one 4 s := rfl

theorem t_k3₁ : ties₁ one 11 (lookupSeat.put s g G) = ties₁ one 10 s := rfl

/-- core₁'s step across the kind's own block of lookup 0: border 4 → 5. -/
theorem c_4_5 (hn : G.next = slots₁ one 0) (hs : G.ns = slots₁ one 0) (hz : PscRun.Sized G)
    (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 4 s = true) :
    core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 5 (lookupSeat.put s g G) =
      true := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 0 s && ((readers₁ one).pile s).isNone) &&
      (!s.base.heard.isSome && s.base.home.size == slots₁ one 0 && _)) = true := h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h'
  have h3 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h2).1).2
  show ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 0 s && ((readers₁ one).pile s).isNone) &&
      (true && s.base.home.size == slots₁ one 0 &&
        (G.next == slots₁ one 0 && G.ns == slots₁ one 0 &&
          (G.vp.size == G.ns && G.mf.size == G.ns && G.gotF.size == G.ns)))) = true
  rw [h1, h3]
  simp [hn, hs, hz.1, hz.2.1, hz.2.2]

/-- core₁'s step across the kind's own block of lookup 1: border 10 → 11. -/
theorem c_10_11 (hn : G.next = slots₁ one 1) (hs : G.ns = slots₁ one 1) (hz : PscRun.Sized G)
    (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 10 s = true) :
    core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 11 (lookupSeat.put s g G) =
      true := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) &&
      (!s.base.heard.isSome && s.base.home.size == slots₁ one 1 && _)) = true := h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h'
  have h3 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h2).1).2
  show ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) &&
      (true && s.base.home.size == slots₁ one 1 &&
        (G.next == slots₁ one 1 && G.ns == slots₁ one 1 &&
          (G.vp.size == G.ns && G.mf.size == G.ns && G.gotF.size == G.ns)))) = true
  rw [h1, h3]
  simp [hn, hs, hz.1, hz.2.1, hz.2.2]

theorem sh_4_5 (hn : G.next = slots₁ one 0) (hs : G.ns = slots₁ one 0) (hz : PscRun.Sized G)
    (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 4 s = true) :
    shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 5 (lookupSeat.put s g G) = true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 4 5 s _
    (fun h => (t_k3₀ one s g G).trans h) (c_4_5 one s g G hn hs hz) h

theorem sh_10_11 (hn : G.next = slots₁ one 1) (hs : G.ns = slots₁ one 1) (hz : PscRun.Sized G)
    (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 10 s = true) :
    shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 11 (lookupSeat.put s g G) =
      true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 10 11 s _
    (fun h => (t_k3₁ one s g G).trans h) (c_10_11 one s g G hn hs hz) h

/-- The table's number of hidden values of lookup l is the face's. -/
theorem slots₁_eq (l : ℕ) (hl : l < one.ranges.lookups.length) :
    slots₁ one l = (faceOfLkp (Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin)
      (Lof one l))).slots := by
  unfold slots₁
  rw [look_at one l hl]
  rfl

section
variable {XI Cells Mm Smp Rec W : Type} {C : _root_.Run.PQ.CK} (F : FileDescription XI) (Fr : Frame)
  (Gr : Reading (Xi × FirstState) Cells Mm Smp Rec) (at_ : Where) (one : OneTime)
  (R : KRead Cells Mm) (coll : Strs → Rec → Prop)
  (hP : ∀ (p : Xi) (s : FirstState) (g : HeardG) (G : Fork),
    SamePins Gr (p, s) (p, lookupSeat.put s g G))

include hP

/-- **The table's promise behind the kind's own block of lookup 0**: border 4 → 5. -/
theorem on_4_5 (pc : Piece C Fr (Xi × FirstState) Claim W)
    (hbase : ∀ j ∈ pinned (open₁ 2 4), (at_ j).1 < pc.base) (hcoll : CollCell coll)
    (a b : (Xi × FirstState) × Fr.E.Str) (τ : Iop.Tr (uLT C pc.ds))
    (hout : pc.ior.red.out a τ = some b) (g : HeardG) (G : Fork)
    (hb : b.1 = (a.1.1, lookupSeat.put a.1.2 g G)) (hn : G.next = slots₁ one 0)
    (hs : G.ns = slots₁ one 0) (hz : PscRun.Sized G) (h : on₁ F Fr Gr at_ one R coll 4 a) :
    on₁ F Fr Gr at_ one R coll 5 b := by
  have h2 := on₁_two F Fr Gr at_ one R coll 4 a h
  obtain ⟨⟨p, s⟩, y⟩ := a
  obtain ⟨b1, y'⟩ := b
  obtain rfl : b1 = (p, lookupSeat.put s g G) := hb
  have Hy := strsStay_of_out F Fr at_ pc (open₁ 2 4) hbase _ _ τ hout
  unfold on₁ at h ⊢
  rw [h2] at h ⊢
  refine onAt_fwd F Gr at_ _ _ _ _ _ _ _ _ _ _ _ (open₁ 2 4) (open₁ 2 5) rfl p s _ _ _ rfl
    (hP p s g G) Hy
    (free₁_step F Gr at_ one R coll 4 5 p s _ _ _ (hP p s g G) hcoll Hy rfl rfl
      (by omega) (fun h18 => absurd h18 (by omega)) (fun _ h => h) fun h => h)
    (sh_4_5 one s g G hn hs hz) h

/-- **The table's promise behind the kind's own block of lookup 1**: border 10 → 11. -/
theorem on_10_11 (pc : Piece C Fr (Xi × FirstState) Claim W)
    (hbase : ∀ j ∈ pinned (open₁ 2 10), (at_ j).1 < pc.base) (hcoll : CollCell coll)
    (a b : (Xi × FirstState) × Fr.E.Str) (τ : Iop.Tr (uLT C pc.ds))
    (hout : pc.ior.red.out a τ = some b) (g : HeardG) (G : Fork)
    (hb : b.1 = (a.1.1, lookupSeat.put a.1.2 g G)) (hn : G.next = slots₁ one 1)
    (hs : G.ns = slots₁ one 1) (hz : PscRun.Sized G) (h : on₁ F Fr Gr at_ one R coll 10 a) :
    on₁ F Fr Gr at_ one R coll 11 b := by
  have h2 := on₁_two F Fr Gr at_ one R coll 10 a h
  obtain ⟨⟨p, s⟩, y⟩ := a
  obtain ⟨b1, y'⟩ := b
  obtain rfl : b1 = (p, lookupSeat.put s g G) := hb
  have Hy := strsStay_of_out F Fr at_ pc (open₁ 2 10) hbase _ _ τ hout
  unfold on₁ at h ⊢
  rw [h2] at h ⊢
  refine onAt_fwd F Gr at_ _ _ _ _ _ _ _ _ _ _ _ (open₁ 2 10) (open₁ 2 11) rfl p s _ _ _ rfl
    (hP p s g G) Hy
    (free₁_step F Gr at_ one R coll 10 11 p s _ _ _ (hP p s g G) hcoll Hy rfl rfl
      (by omega) (fun h18 => absurd h18 (by omega)) (fun _ h => h) fun h => h)
    (sh_10_11 one s g G hn hs hz) h

end

/-- The table's reading at the first chain does not read what the kind's block writes. -/
theorem samePins_put {Cells Mm Smp Rec : Type} (B : BaseSt Cells Mm Smp Rec) (p : Xi)
    (s : FirstState) (g : HeardG) (G : Fork) : SamePins B.h₁ (p, s) (p, lookupSeat.put s g G) :=
  ⟨fun _ _ => rfl, rfl⟩

end Johnson.RunOne.Law.TieBehind

#print axioms Johnson.RunOne.Law.TieBehind.sh_4_5
#print axioms Johnson.RunOne.Law.TieBehind.sh_10_11
#print axioms Johnson.RunOne.Law.TieBehind.slots₁_eq
#print axioms Johnson.RunOne.Law.TieBehind.on_4_5
#print axioms Johnson.RunOne.Law.TieBehind.on_10_11
#print axioms Johnson.RunOne.Law.TieBehind.samePins_put
