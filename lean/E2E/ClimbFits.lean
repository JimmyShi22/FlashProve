-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbFits.lean: the wires of a written file and of the written link say, of proof of work, what
the pairs with bits of E2E/ClimbWhole.lean and E2E/ClimbLink.lean say.

The compiler speaks of proof of work through the test data that a round's wire may hold (`GrW`,
OnBytes/TypedOracleCompiler/Iop/BatchWire.lean): `RoundsQueryLayout.pass` (all test bits are 0), `RoundsQueryLayout.zero` (all test bits
set to 0), and the relation `Puts` (OnBytes/Prover/Inv.lean: one transcript is another but for
numbers written in as nonces). A pair with bits speaks of it through `passR`, `zeroR`, `oldR` and
`strip` (E2E/ClimbRun.lean, E2E/ClimbPair.lean). `Fits p A' W` says, round by round: the wire's test
is the pair's; a verifier message with the test bits set to 0 is the pair's `zero` of its old part;
and two prover messages that differ by a number written in as a nonce are the same when stripped.
The third goes one way: that two messages with the same stripped form differ by a nonce alone is not
asked.

  `Fits.pass`: the wire's tests are passed exactly if all verifier messages pass the pair's.
  `Fits.zero_eq`: verifier randomness with all test bits set to 0 is the image of its old part.
    `Fits.zero`: so its old part is as it was.
  `Fits.puts`: a transcript that is another but for nonces is, stripped, the same.
  `puts_refl`: a transcript is itself but for nonces.
  `fits_app`, `fits_cons`: two wires in a row; a round kept as it is, under a wire with no test.
  `grPass`, `pass_lo_eq`, `pass_sh_eq`: a round's test, read off its test data.
  `grPass_grOf`, `zeroOf_grOf`, `old_putOf`: the written test data (`grOf` at `Dn`), by the number
    of bits. `rpZ_pass_lo`, `rpZ_pass_sh`, `rpZ_zero_lo`, `rpZ_zero_sh`, `rpZ_strip_eq`: one written
    round, local or shared.
  `fits_wiresSL`, `fits_wiresLo`, `fits_wiresSh`; `fits_wqWhole`, `fits_wqW`: the written chains,
    the wire of a whole file, the wire of the link. They hold at every kit that does not read an
    entry's proof of work (`KitFree`) and at all rounds' data.

The walk over the wires follows that of `PutsFree` in Johnson/Prover/Law/PutsAt.lean. That file is
not reviewed; nor are Johnson/Prover/Law/Chain.lean, which this one imports, and
OnBytes/Prover/Inv.lean, which it reaches through that one.

Limits.
  * Words alone: nothing here says that a verifier accepts or rejects anything.
  * `Fits` reads of a round's test data the test, `set` at bits 0 and `put`. It does not read
    `more`, `get` or `b`, nor how hash blocks give a verifier message (`chal`).
  * That the wiring of the three files' protocols of the full size is made of `wqWhole` and of a
    wire with the rounds' wires of `wqW` (`sibW`, Johnson/Top/EntrySib.lean) is not said here:
    E2E/ClimbAccLawAtD.lean.
  * Nothing on probability, views or zero knowledge.

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.

-/
import E2E.ClimbRun
import E2E.ClimbWhole
import E2E.ClimbLink
import Johnson.Prover.Law.Chain
import OnBytes.Maker.Wire
import Johnson.RunOne.StrictLinkW

set_option autoImplicit false

namespace AtPublicFiles.Climb
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Prover OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK PlainOf Dn View XO)
open TypedOracleCompiler.Run.PQ (RD roundS wiresSL)

variable {lam K : ℕ}

/-! ## 1. The predicate, and what it gives -/

/-- A wire says the pair's words, round by round: the wire's test is the pair's; a verifier message
with the test bits set to 0 is the pair's `zero` of its old part; and a prover message that differs
from another by a number written in as a nonce alone is, stripped, the same. -/
def Fits : {s t : Shape} → Pair s t → (A' : RoundSplits t) → RoundsQueryLayout lam K t A' → Prop
  | [], [], _, _, _ => True
  | [], _ :: _, p, _, _ => Empty.elim p
  | _ :: _, [], p, _, _ => Empty.elim p
  | _ :: _, r' :: _, (u, p), (a', A'), (w, W) =>
      (∀ c', w.pass c' = u.pass c') ∧ (∀ c', w.zero c' = u.zero (u.old c')) ∧
      (∀ m m' : r'.Msg, m'.1 = m.1 →
        (m'.2 = m.2 ∨
          (∃ g n, a'.kind = .lo ∧ w.grJ = some g ∧
            m'.2 = a'.plain.symm ((a'.plain m.2).1, g.put n (a'.plain m.2).2)) ∨
          (∃ g n, a'.kind = .sh ∧ w.gr0 = some g ∧
            m'.2 = a'.plain.symm (g.put n (a'.plain m.2).1, (a'.plain m.2).2))) →
        u.strip m' = u.strip m) ∧
      Fits p A' W

/-- All the wire's tests are passed exactly if all verifier messages pass the pair's. -/
theorem Fits.pass : ∀ {s t : Shape} {p : Pair s t} {A' : RoundSplits t} {W : RoundsQueryLayout lam K t A'},
    Fits p A' W → ∀ ρ' : Rho t, RoundsQueryLayout.pass t A' W ρ' = p.passR ρ'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, p, _, _, _, _ => Empty.elim p
  | _ :: _, [], p, _, _, _, _ => Empty.elim p
  | _ :: _, _ :: t, (u, p), (_, A'), (w, W), h, (c', ρ') => by
      show (w.pass c' && RoundsQueryLayout.pass t A' W ρ') = (u.pass c' && p.passR ρ')
      rw [h.1 c', Fits.pass h.2.2.2 ρ']

/-- **Verifier randomness with all test bits set to 0 is the image of its old part.** -/
theorem Fits.zero_eq : ∀ {s t : Shape} {p : Pair s t} {A' : RoundSplits t} {W : RoundsQueryLayout lam K t A'},
    Fits p A' W → ∀ ρ' : Rho t, RoundsQueryLayout.zero t A' W ρ' = p.zeroR (p.oldR ρ')
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, p, _, _, _, _ => Empty.elim p
  | _ :: _, [], p, _, _, _, _ => Empty.elim p
  | _ :: _, _ :: t, (u, p), (_, A'), (w, W), h, (c', ρ') => by
      show (w.zero c', RoundsQueryLayout.zero t A' W ρ') = (u.zero (u.old c'), p.zeroR (p.oldR ρ'))
      rw [h.2.1 c', Fits.zero_eq h.2.2.2 ρ']

/-- So to set all test bits to 0 leaves the old part of the verifier randomness as it was. -/
theorem Fits.zero {s t : Shape} {p : Pair s t} {A' : RoundSplits t} {W : RoundsQueryLayout lam K t A'}
    (h : Fits p A' W) (ρ' : Rho t) : p.oldR (RoundsQueryLayout.zero t A' W ρ') = p.oldR ρ' := by
  rw [h.zero_eq, p.oldR_zeroR]

/-- A transcript that is another but for nonces is, stripped, the same. -/
theorem Fits.puts : ∀ {s t : Shape} {p : Pair s t} {A' : RoundSplits t} {W : RoundsQueryLayout lam K t A'},
    Fits p A' W → ∀ τ τ' : Tr t, Puts t A' W τ τ' → p.strip τ' = p.strip τ
  | [], [], _, _, _, _, _, _, _ => rfl
  | [], _ :: _, p, _, _, _, _, _, _ => Empty.elim p
  | _ :: _, [], p, _, _, _, _, _, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (_, _), (_, _), h, (m, c, τ), (m', c', τ'), hP => by
      show (u.strip m', u.old c', p.strip τ') = (u.strip m, u.old c, p.strip τ)
      rw [h.2.2.1 m m' hP.1 hP.2.2.1, hP.2.1, Fits.puts h.2.2.2 τ τ' hP.2.2.2]

/-- A transcript is itself but for nonces. -/
theorem puts_refl : ∀ (t : Shape) (A' : RoundSplits t) (W : RoundsQueryLayout lam K t A') (τ : Tr t),
    Puts t A' W τ τ
  | [], _, _, _ => trivial
  | _ :: t, (_, A'), (_, W), (_, _, τ) => ⟨rfl, rfl, Or.inl rfl, puts_refl t A' W τ⟩

/-! ## 2. Putting wires together -/

/-- Two pairs in a row, under two wires in a row. -/
theorem fits_app : ∀ {s t s' t' : Shape} {p : Pair s t} {p' : Pair s' t'} {A' : RoundSplits t}
    {B' : RoundSplits t'} {W : RoundsQueryLayout lam K t A'} {V : RoundsQueryLayout lam K t' B'},
    Fits p A' W → Fits p' B' V → Fits (Pair.app p p') (RoundSplits.app A' B') (WireSB.app W V)
  | [], [], _, _, _, _, _, _, _, _, _, hV => hV
  | [], _ :: _, _, _, p, _, _, _, _, _, _, _ => Empty.elim p
  | _ :: _, [], _, _, p, _, _, _, _, _, _, _ => Empty.elim p
  | _ :: _, _ :: _, _, _, (_, _), _, (_, _), _, (_, _), _, hW, hV =>
    ⟨hW.1, hW.2.1, hW.2.2.1, fits_app hW.2.2.2 hV⟩

/-- A round kept as it is, under a wire that has no test. -/
theorem fits_cons (r : Round) (a : RAnn r) (w : WireRB lam K r a) (h0 : w.gr0 = none)
    (hJ : w.grJ = none) {s t : Shape} {p : Pair s t} {A' : RoundSplits t} {W : RoundsQueryLayout lam K t A'}
    (h : Fits p A' W) :
    Fits (s := r :: s) (t := r :: t) (Pair.cons r p) (a, A') (w, W) := by
  refine ⟨fun c' => ?_, fun c' => ?_, fun m m' h1 h3 => ?_, h⟩
  · show w.pass c' = true
    cases hk : a.kind with
    | lo => exact pass_lo hk (Or.inl hJ)
    | sh => exact pass_sh hk (Or.inl h0)
  · show w.zero c' = c'
    cases hk : a.kind with
    | lo => rw [zero_lo w hk, hJ]; rfl
    | sh => rw [zero_sh w hk, h0]; rfl
  · show m' = m
    rcases h3 with h3 | ⟨g, _, _, hg, _⟩ | ⟨g, _, _, hg, _⟩
    · exact Prod.ext h1 h3
    · rw [hJ] at hg
      cases hg
    · rw [h0] at hg
      cases hg

/-! ## 3. A round's test data, by the number of bits -/

/-- A round's test, read off its test data; true where there are none. -/
def grPass {Cc P : Type} : Option (GrW Cc P) → Cc → Bool
  | none, _ => true
  | some g, c => g.ok c

theorem pass_lo_eq {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .lo)
    (c : r.Chal) : w.pass c = grPass w.grJ c := by
  unfold TypedOracleCompiler.Iop.WireRB.pass
  rw [hk]
  cases w.grJ <;> rfl

theorem pass_sh_eq {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .sh)
    (c : r.Chal) : w.pass c = grPass w.gr0 c := by
  unfold TypedOracleCompiler.Iop.WireRB.pass
  rw [hk]
  cases w.gr0 <;> rfl

/-- The written test is the proof-of-work check. -/
theorem grPass_grOf {Cc P : Type} : ∀ (b : ℕ) (c : GChal b Cc),
    grPass ((_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr) c = GChal.pass c
  | 0, c => (GChal.pass_zero_bits c).symm
  | b + 1, c => _root_.Iop.GrW.ok_ofBits Dn b Cc P c

/-- A verifier message with the written test bits set to 0 is its old part with bits 0 put in. -/
theorem zeroOf_grOf {Cc P : Type} : ∀ (b : ℕ) (c : GChal b Cc),
    zeroOf ((_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr) c = GChal.zero b (GChal.old c)
  | 0, _ => rfl
  | _ + 1, _ => rfl

/-- To write a number in by the written test data leaves the plain part behind the nonce as it
was. -/
theorem old_putOf {Cc P : Type} :
    ∀ (b : ℕ) (g : GrW (GChal b Cc) (GPlain ℕ b P)) (n : ℕ) (pl : GPlain ℕ b P),
      (_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr = some g →
      GPlain.old (g.put n pl) = GPlain.old pl
  | 0, _, _, _, e => by cases e
  | b + 1, g, _, _, e => by
    obtain rfl : TypedOracleCompiler.Tagged.ofGr (_root_.Iop.GrW.ofBits Dn b Cc P) = g := Option.some.inj e
    rfl

/-! ## 4. One written round, local or shared -/

section
variable (C : CK) (Kf : KitFree C) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD)

theorem rpZ_pass_lo (c' : (roundS C d).up.Chal) :
    (TypedOracleCompiler.Run.PQ.wireS C K chal d).pass c' = (rpZ C Kf d).pass c' :=
  (pass_lo_eq (TypedOracleCompiler.Run.PQ.wireS C K chal d) rfl c').trans
    (grPass_grOf (Cc := C.Ch d.entry d.kind) (P := PlainOf d.items) d.entry.work c')

theorem rpZ_pass_sh (c' : (roundS C d).up.Chal) :
    (TypedOracleCompiler.Slice.wireSh C K chal d).pass c' = (rpZ C Kf d).pass c' :=
  (pass_sh_eq (TypedOracleCompiler.Slice.wireSh C K chal d) rfl c').trans
    (grPass_grOf (Cc := C.Ch d.entry d.kind) (P := PlainOf d.items) d.entry.work c')

theorem rpZ_zero_lo (c' : (roundS C d).up.Chal) :
    (TypedOracleCompiler.Run.PQ.wireS C K chal d).zero c' = (rpZ C Kf d).zero ((rpZ C Kf d).old c') :=
  (zero_lo (TypedOracleCompiler.Run.PQ.wireS C K chal d) rfl c').trans
    ((zeroOf_grOf (Cc := C.Ch d.entry d.kind) (P := PlainOf d.items) d.entry.work c').trans
      (congrArg (GChal.zero d.entry.work)
        (Equiv.apply_symm_apply (Kf.eqv d.entry d.kind) (GChal.old (b := d.entry.work) c')).symm))

theorem rpZ_zero_sh (c' : (roundS C d).up.Chal) :
    (TypedOracleCompiler.Slice.wireSh C K chal d).zero c' = (rpZ C Kf d).zero ((rpZ C Kf d).old c') :=
  (zero_sh (TypedOracleCompiler.Slice.wireSh C K chal d) rfl c').trans
    ((zeroOf_grOf (Cc := C.Ch d.entry d.kind) (P := PlainOf d.items) d.entry.work c').trans
      (congrArg (GChal.zero d.entry.work)
        (Equiv.apply_symm_apply (Kf.eqv d.entry d.kind) (GChal.old (b := d.entry.work) c')).symm))

/-- Two messages with the same oracle part whose plain parts are the same behind the nonce are,
stripped, the same. -/
theorem rpZ_strip_eq (m m' : (roundS C d).up.Msg) (h1 : m'.1 = m.1)
    (h2 : GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) m'.2 =
      GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) m.2) :
    (rpZ C Kf d).strip m' = (rpZ C Kf d).strip m :=
  Prod.ext h1 h2

end

/-! ## 5. The written chains, a file's wire, the link's wire -/

section
variable (C : CK) (Kf : KitFree C) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- The link's written rounds. -/
theorem fits_wiresSL : ∀ ds : List RD, Fits (pairZ C Kf (z0 ds)) _ (wiresSL C K chal ds)
  | [] => trivial
  | d :: ds =>
    ⟨rpZ_pass_lo C Kf K chal d, rpZ_zero_lo C Kf K chal d, fun m m' h1 h3 =>
      rpZ_strip_eq C Kf d m m' h1 (by
        rcases h3 with h3 | ⟨g, n, -, e, e'⟩ | ⟨g, n, -, e, -⟩
        · rw [h3]
        · exact (congrArg (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items)) e').trans
            (old_putOf (Cc := C.Ch d.entry d.kind) d.entry.work g n m.2 e)
        · cases e),
      fits_wiresSL ds⟩

/-- A file's written rounds that are local. -/
theorem fits_wiresLo : ∀ ds : List RDT, Fits (pairT C Kf ds) _ (wiresLo C K chal ds)
  | [] => trivial
  | d :: ds =>
    ⟨rpZ_pass_lo C Kf K chal d.toRD, rpZ_zero_lo C Kf K chal d.toRD, fun m m' h1 h3 =>
      rpZ_strip_eq C Kf d.toRD m m' h1 (by
        rcases h3 with h3 | ⟨g, n, -, e, e'⟩ | ⟨g, n, -, e, -⟩
        · rw [h3]
        · exact (congrArg (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items)) e').trans
            (old_putOf (Cc := C.Ch d.entry d.kind) d.entry.work g n m.2 e)
        · cases e),
      fits_wiresLo ds⟩

/-- A file's written rounds that are shared. -/
theorem fits_wiresSh : ∀ ds : List RDT, Fits (pairT C Kf ds) _ (wiresSh C K chal ds)
  | [] => trivial
  | d :: ds =>
    ⟨rpZ_pass_sh C Kf K chal d.toRD, rpZ_zero_sh C Kf K chal d.toRD, fun m m' h1 h3 =>
      rpZ_strip_eq C Kf d.toRD m m' h1 (by
        rcases h3 with h3 | ⟨g, n, -, e, -⟩ | ⟨g, n, -, e, e'⟩
        · rw [h3]
        · cases e
        · exact (congrArg (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items)) e').trans
            (old_putOf (Cc := C.Ch d.entry d.kind) d.entry.work g n m.2 e)),
      fits_wiresSh ds⟩

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The wire of a whole written file says the words of the file's pair.** -/
theorem fits_wqWhole :
    Fits (pairW C Kf D tF tJ t3) _ (wqWhole C K chal D tF tJ t3 silent run).sh := by
  refine fits_cons _ _ _ rfl rfl (fits_app (fits_wiresLo C Kf K chal D.ds₁) ?_)
  refine fits_cons _ _ _ rfl rfl (fits_app (fits_wiresSh C Kf K chal D.ds₂) ?_)
  exact fits_cons _ _ _ rfl rfl (fits_wiresLo C Kf K chal D.ds₃)

variable (ds : List RD) (a : ℕ) (xs : List XO) {Y : Type} (dec : Y → View → Bool)

/-- **The wire of the written link says the words of the link's pair.** -/
theorem fits_wqW :
    Fits (pairL C Kf ds) _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh :=
  fits_cons _ _ _ rfl rfl (fits_wiresSL C Kf K chal ds)

end

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.Fits.pass
#print axioms AtPublicFiles.Climb.Fits.zero_eq
#print axioms AtPublicFiles.Climb.Fits.zero
#print axioms AtPublicFiles.Climb.Fits.puts
#print axioms AtPublicFiles.Climb.puts_refl
#print axioms AtPublicFiles.Climb.fits_app
#print axioms AtPublicFiles.Climb.fits_cons
#print axioms AtPublicFiles.Climb.pass_lo_eq
#print axioms AtPublicFiles.Climb.pass_sh_eq
#print axioms AtPublicFiles.Climb.grPass_grOf
#print axioms AtPublicFiles.Climb.zeroOf_grOf
#print axioms AtPublicFiles.Climb.old_putOf
#print axioms AtPublicFiles.Climb.rpZ_pass_lo
#print axioms AtPublicFiles.Climb.rpZ_pass_sh
#print axioms AtPublicFiles.Climb.rpZ_zero_lo
#print axioms AtPublicFiles.Climb.rpZ_zero_sh
#print axioms AtPublicFiles.Climb.rpZ_strip_eq
#print axioms AtPublicFiles.Climb.fits_wiresSL
#print axioms AtPublicFiles.Climb.fits_wiresLo
#print axioms AtPublicFiles.Climb.fits_wiresSh
#print axioms AtPublicFiles.Climb.fits_wqWhole
#print axioms AtPublicFiles.Climb.fits_wqW
