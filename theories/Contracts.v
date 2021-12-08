(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From MinimalCaps Require Import
     Machine.

From Coq Require Import
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Sep.Spec
     Symbolic.Mutator
     Syntax.
From Katamaran Require
     Environment
     Sep.Logic.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Inductive PurePredicate : Set :=
| subperm
.

Inductive Predicate : Set :=
  ptsreg
| ptsto
| safe
| dummy
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for PurePredicate.
  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for PurePredicate.
Derive EqDec for Predicate.

Module Export MinCapsAssertionKit <:
  (AssertionKit MinCapsTermKit MinCapsProgramKit).

  Export MinCapsProgramKit.

  Definition 𝑷 := PurePredicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | subperm => [ty_perm, ty_perm]
    end.

  Definition decide_subperm (p p' : Lit ty_perm) : bool :=
    match p with
    | O => true
    | R => match p' with
           | O => false
           | _ => true
           end
    | RW => match p' with
            | RW => true
            | _ => false
            end
    end.

  Definition Subperm (p p' : Lit ty_perm) : Prop :=
    decide_subperm p p' = true.

  Definition 𝑷_inst (p : 𝑷) : abstract Lit (𝑷_Ty p) Prop :=
    match p with
    | subperm => Subperm
    end.

  Instance 𝑷_eq_dec : EqDec 𝑷 := PurePredicate_eqdec.

  Definition 𝑯 := Predicate.
  Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
    match p with
    | ptsreg => [ty_enum regname, ty_word]
    | ptsto => [ty_addr, ty_memval]
    | safe => [ty_word]
    | dummy => [ty_cap]
    end.
  Instance 𝑯_is_dup : IsDuplicable Predicate := {
    is_duplicable p :=
      match p with
      | ptsreg => false
      | ptsto => false
      | safe => true
      | dummy => false
      end
    }.
  Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.
End MinCapsAssertionKit.

Module MinCapsSymbolicContractKit <:
  SymbolicContractKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.
  Module Export ASS := Assertions MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.

  Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
  Local Notation "p '∗' q" := (asn_sep p q) (at level 150).

  Open Scope env_scope.

  Local Notation "p '<=ₚ' p'" := (asn_formula (formula_user subperm (env_nil ► (ty_perm ↦ p) ► (ty_perm ↦ p')))) (at level 100).

  Local Notation "r '↦r' t" := (asn_chunk (chunk_user ptsreg (env_nil ► (ty_enum regname ↦ r) ► (ty_word ↦ t)))) (at level 100).
  Local Notation "a '↦m' t" := (asn_chunk (chunk_user ptsto (env_nil ► (ty_addr ↦ a) ► (ty_int ↦ t)))) (at level 100).
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty_unit opt xl alt_inl "_" alt_inr).
  Local Notation asn_safe w := (asn_chunk (chunk_user safe (env_nil ► (ty_word ↦ w)))).
  Local Notation asn_csafe c := (asn_chunk (chunk_user safe (env_nil ► (ty_word ↦ (term_inr c))))).
  Local Notation asn_dummy c := (asn_chunk (chunk_user dummy (env_nil ► (ty_cap ↦ c)))).
  Local Notation asn_match_cap c p b e a asn :=
    (asn_match_record
       capability c
       (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
        "cap_permission" p)
        "cap_begin" b)
        "cap_end" e)
        "cap_cursor" a)
       asn).
  Local Notation asn_within_bounds a b e :=
    (asn_formula (formula_bool (term_binop binop_and
                              (term_binop binop_le b a)
                              (term_binop binop_le a e)))).

  (* Arguments asn_prop [_] & _. *)

  Definition sep_contract_logvars (Δ : PCtx) (Σ : LCtx) : LCtx :=
    ctx_map (fun '(x::σ) => x::σ) Δ ▻▻ Σ.

  Definition create_localstore (Δ : PCtx) (Σ : LCtx) : SStore Δ (sep_contract_logvars Δ Σ) :=
    (env_tabulate (fun '(x::σ) xIn =>
                     @term_var
                       (sep_contract_logvars Δ Σ)
                       x
                       σ
                       (inctx_cat_left Σ (inctx_map (fun '(y::τ) => y::τ) xIn)))).


  (* regInv(r) = ∃ w : word. r ↦ w * safe(w) *)
  Definition regInv {Σ} (r : RegName) (w : string) : Assertion Σ :=
    asn_exist w ty_word
              (term_lit (ty_enum regname) r ↦r (@term_var _ _ _ inctx_zero) ∗
                asn_safe (@term_var _ _ _ inctx_zero)).

  (* regInv(r) = ∃ c : cap. r ↦ c * csafe(c) *)
  Definition regInvCap {Σ} (r : Reg ty_cap) : Assertion Σ :=
    asn_exist "c" ty_cap
              (r ↦ term_var "c" ∗
                 asn_csafe (term_var "c")).

  (* mach_inv = regInv(r1) * regInv(r2) * regInv(r3) * regInv(r4) * regInvCap(pc) *)
  Definition mach_inv {Σ} : Assertion Σ :=
    (regInv R0 "w0") ∗ (regInv R1 "w1") ∗ (regInvCap pc).
    (* ✱ (regInv R2 "w2") ✱ (regInv R3 "w3") *)

  (*
     @pre mach_inv;
     @post mach_inv;
     τ f(Δ...) *)
  Definition mach_inv_contract {Δ τ} : SepContract Δ τ :=
    {| sep_contract_logic_variables := sep_contract_logvars Δ ε;
       sep_contract_localstore      := create_localstore Δ ε;
       sep_contract_precondition    := mach_inv;
       sep_contract_result          := "result_mach_inv";
       sep_contract_postcondition   := mach_inv;
    |}.

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepLemma {Δ} (f : Lem Δ) : Type :=
    Lemma Δ.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition sep_contract_read_reg : SepContractFun read_reg :=
    {| sep_contract_logic_variables := ["rreg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "rreg"]%arg;
       sep_contract_precondition    := term_var "rreg" ↦r term_var "w";
       sep_contract_result          := "result_read_reg";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_read_reg") (term_var "w") ∗
                term_var "rreg" ↦r term_var "w";
    |}.

  Definition sep_contract_read_reg_cap : SepContractFun read_reg_cap :=
    {| sep_contract_logic_variables := ["creg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "creg"]%arg;
       sep_contract_precondition    := term_var "creg" ↦r term_var "w";
       sep_contract_result          := "result_read_reg_cap";
       sep_contract_postcondition   :=
         asn_exist "c" ty_cap
                   (asn_eq (term_var "result_read_reg_cap") (term_var "c") ∗
                           asn_eq (term_var "w") (term_inr (term_var "c")) ∗
                           term_var "creg" ↦r (term_var "w"));
    |}.

  Definition sep_contract_read_reg_num : SepContractFun read_reg_num :=
    {| sep_contract_logic_variables := ["nreg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "nreg"]%arg;
       sep_contract_precondition    := term_var "nreg" ↦r term_var "w";
       sep_contract_result          := "result_read_reg_num";
       sep_contract_postcondition   :=
         asn_exist "i" ty_int
                   (asn_eq (term_var "result_read_reg_num") (term_var "i") ∗
                           asn_eq (term_var "w") (term_inl (term_var "i")) ∗
                           term_var "nreg" ↦r term_var "w");
    |}.

  Definition sep_contract_write_reg : SepContract ["wreg" ∶ ty_enum regname, "w"  ∶ ty_word] ty_unit :=
    {| sep_contract_logic_variables := ["wreg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "wreg", term_var "w"]%arg;
       sep_contract_precondition    := asn_exist "old_word" ty_word (term_var "wreg" ↦r term_var "old_word");
       sep_contract_result          := "result_write_reg";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_write_reg") (term_lit ty_unit tt) ∗
                term_var "wreg" ↦r term_var "w";
    |}.

  Definition sep_contract_next_pc : SepContract ctx_nil ty_cap :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap];
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := pc ↦ term_var "opc";
       sep_contract_result          := "result_next_pc";
       sep_contract_postcondition   :=
         pc ↦ term_var "opc" ∗
            asn_match_cap (term_var "opc") "perm" "beg" "end" "cur"
            (asn_eq
               (term_var "result_next_pc")
               (term_record capability
                            [term_var "perm",
                             term_var "beg",
                             term_var "end",
                             term_binop binop_plus (term_var "cur") (term_lit ty_addr 1)]))
    |}.

  Definition sep_contract_update_pc : SepContract ctx_nil ty_unit :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap];
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := pc ↦ term_var "opc" ∗ asn_csafe (term_var "opc");
       sep_contract_result          := "result_update_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_update_pc") (term_lit ty_unit tt) ∗
                asn_exist "npc" ty_cap
                (pc ↦ term_var "npc" ∗ asn_csafe (term_var "npc"));
    |}.

  Definition sep_contract_add_pc : SepContract ["offset" ∶ ty_int] ty_unit :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap, "offset" ∶ ty_int];
       sep_contract_localstore      := [term_var "offset"]%arg;
       sep_contract_precondition    := pc ↦ term_var "opc" ∗ asn_csafe (term_var "opc");
       sep_contract_result          := "result_add_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_add_pc") (term_lit ty_unit tt) ∗
                asn_exist "npc" ty_cap
                (pc ↦ term_var "npc" ∗ asn_csafe (term_var "npc"));
    |}.

  Definition sep_contract_read_mem : SepContract ["c" ∶ ty_cap ] ty_memval :=
    {| sep_contract_logic_variables := ["c" ∶ ty_cap];
       sep_contract_localstore      := [term_var "c"]%arg;
       sep_contract_precondition    := asn_csafe (term_var "c");
       sep_contract_result          := "read_mem_result";
       sep_contract_postcondition   :=
         asn_csafe (term_var "c") ∗ asn_safe (term_var "read_mem_result")
    |}.

  Definition sep_contract_write_mem : SepContract ["c" ∶ ty_cap, "v" ∶ ty_memval ] ty_unit :=
    {| sep_contract_logic_variables := ["c" ∶ ty_cap, "v" ∶ ty_memval];
       sep_contract_localstore      := [term_var "c", term_var "v"]%arg;
       sep_contract_precondition    := asn_safe (term_var "v") ∗ asn_csafe (term_var "c");
       sep_contract_result          := "write_mem_result";
       sep_contract_postcondition   :=
         asn_csafe (term_var "c") ∗ asn_eq (term_var "write_mem_result") (term_lit ty_unit tt);
    |}.

  Definition sep_contract_read_allowed : SepContract ["p" ∶ ty_perm ] ty_bool :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_read_allowed";
       sep_contract_postcondition   := 
         asn_if (term_var "result_read_allowed")
                (term_lit ty_perm R <=ₚ term_var "p")
                (asn_eq (term_var "result_read_allowed") (term_lit ty_bool false));
    |}.

  Definition sep_contract_write_allowed : SepContract ["p" ∶ ty_perm ] ty_bool :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_write_allowed";
       sep_contract_postcondition   :=
         asn_if (term_var "result_write_allowed")
                (term_lit ty_perm RW <=ₚ term_var "p")
                (asn_eq (term_var "result_write_allowed") (term_lit ty_bool false));
    |}.

  Definition sep_contract_upper_bound : SepContract ["a" ∶ ty_addr, "e" ∶ ty_addr ] ty_bool :=
    {| sep_contract_logic_variables := ["a" ∶ ty_addr, "e" ∶ ty_addr ];
       sep_contract_localstore      := [term_var "a", term_var "e"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_upper_bound";
       sep_contract_postcondition   := 
         (asn_eq (term_var "result_upper_bound")
                 (term_binop binop_le (term_var "a") (term_var "e")));
    |}.

  (* 
      @pre true;
      @post ∃ b,e,a,p. c = mkcap(b,e,a,p) ∧ result = (a >= b && (e = none ∨ e = inl e' ∧ e' >= a));
      bool within_bounds(c : capability);
   *)
  Definition sep_contract_within_bounds : SepContract ["c" ∶ ty_cap] ty_bool := 
    {| sep_contract_logic_variables := ["c" ∶ ty_cap];
       sep_contract_localstore      := [term_var "c"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_within_bounds";
       sep_contract_postcondition   :=
         asn_match_cap (term_var "c") "perm" "b" "e" "a"
                       (asn_eq (term_var "result_within_bounds")
                               (term_binop binop_and
                                           (term_binop binop_le (term_var "b") (term_var "a"))
                                           (term_binop binop_le (term_var "a") (term_var "e"))));
    |}.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_jr(lv : lv) *)
  Definition sep_contract_exec_jr : SepContractFun exec_jr :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_jalr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_jalr : SepContractFun exec_jalr :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_j(offset : Z) *)
  Definition sep_contract_exec_j : SepContractFun exec_j :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_jal(lv : lv, offset : Z) *)
  Definition sep_contract_exec_jal : SepContractFun exec_jal :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_bnez(lv : lv, immediate : Z) *)
  Definition sep_contract_exec_bnez : SepContractFun exec_bnez :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_mv(lv : lv, hv : ty_hv) *)
  Definition sep_contract_exec_mv : SepContractFun exec_mv :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_ld(lv : lv, hv : memval, immediate : Z) *)
  Definition sep_contract_exec_ld : SepContractFun exec_ld :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_sd(hv : memval, lv : lv, immediate : Z) *)
  Definition sep_contract_exec_sd : SepContractFun exec_sd :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_lea(lv : lv, hv : ty_hv) *)
  Definition sep_contract_exec_lea : SepContractFun exec_lea :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_restrict(lv : lv, hv : ty_hv) *)
  Definition sep_contract_exec_restrict : SepContractFun exec_restrict :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_restricti(lv : lv, immediate : Z) *)
  Definition sep_contract_exec_restricti : SepContractFun exec_restricti :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_subseg(lv : lv, hv1 hv2 : ty_hv) *)
  Definition sep_contract_exec_subseg : SepContractFun exec_subseg :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_subsegi(lv : lv, hv : ty_hv, immediate : Z) *)
  Definition sep_contract_exec_subsegi : SepContractFun exec_subsegi :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_addi(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_addi : SepContractFun exec_addi :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_add(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_add : SepContractFun exec_add :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_sub(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_sub : SepContractFun exec_sub :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_slt(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_slt : SepContractFun exec_slt :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_slti(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_slti : SepContractFun exec_slti :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_sltu(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_sltu : SepContractFun exec_sltu :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_sltiu(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_sltiu : SepContractFun exec_sltiu :=
    mach_inv_contract.

  (*
      @pre true;
      @post true;
      int perm_to_bits(p : perm) *)
  Definition sep_contract_perm_to_bits : SepContractFun perm_to_bits :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post true;
      int perm_from_bits(i : Z) *)
  Definition sep_contract_perm_from_bits : SepContractFun perm_from_bits :=
    {| sep_contract_logic_variables := ["i" ∶ ty_int];
       sep_contract_localstore      := [term_var "i"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post true;
      int abs(i : int) *)
  Definition sep_contract_abs : SepContractFun abs :=
    {| sep_contract_logic_variables := ["i" ∶ ty_int];
       sep_contract_localstore      := [term_var "i"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post if p <= p' then (result = true ✱ p ≤ p') else result = false;
      int is_sub_perm(p : perm, p' : perm) *)
  Definition sep_contract_is_sub_perm : SepContractFun is_sub_perm :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm, "p'" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p", term_var "p'"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_sub_perm";
       sep_contract_postcondition   :=
         asn_if (term_var "result_is_sub_perm")
                (term_var "p" <=ₚ term_var "p'")
                (asn_eq (term_var "result_is_sub_perm") (term_lit ty_bool false));
    |}.

  (*
      @pre true;
      @post result = (b ≤ b' && e' ≤ e) ;
      bool is_within_range(b' e' b e : Addr) *)
  Definition sep_contract_is_within_range : SepContractFun is_within_range :=
    {| sep_contract_logic_variables := ["b'" ∶ ty_addr, "e'" ∶ ty_addr,
                                        "b" ∶ ty_addr, "e" ∶ ty_addr];
       sep_contract_localstore      := [term_var "b'", term_var "e'", term_var "b", term_var "e"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_within_range";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_is_within_range")
                (term_binop binop_and
                            (term_binop binop_le (term_var "b") (term_var "b'"))
                            (term_binop binop_le (term_var "e'") (term_var "e")))
    |}.
  
  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_isptr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_isptr : SepContractFun exec_isptr :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_getp(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_getp : SepContractFun exec_getp :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_getb(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_getb : SepContractFun exec_getb :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_gete(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_gete : SepContractFun exec_gete :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_geta(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_geta : SepContractFun exec_geta :=
    mach_inv_contract.

  (* @pre mach_inv;
     @post mach_inv;
     bool exec_fail *)
  Definition sep_contract_exec_fail : SepContractFun exec_fail :=
    mach_inv_contract.

  (* @pre mach_inv;
     @post mach_inv;
     bool exec_ret *)
  Definition sep_contract_exec_ret : SepContractFun exec_ret :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec_instr(i : instr) *)
  Definition sep_contract_exec_instr : SepContractFun exec_instr :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      bool exec *)
  Definition sep_contract_exec : SepContractFun exec :=
    mach_inv_contract.

  (*
      @pre mach_inv;
      @post mach_inv;
      unit loop *)
  Definition sep_contract_loop : SepContractFun loop :=
    mach_inv_contract.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | read_allowed    => Some sep_contract_read_allowed
      | write_allowed   => Some sep_contract_write_allowed
      | upper_bound     => Some sep_contract_upper_bound
      | within_bounds   => Some sep_contract_within_bounds
      | read_reg        => Some sep_contract_read_reg
      | read_reg_cap    => Some sep_contract_read_reg_cap
      | read_reg_num    => Some sep_contract_read_reg_num
      | write_reg       => Some sep_contract_write_reg
      | next_pc         => Some sep_contract_next_pc
      | add_pc          => Some sep_contract_add_pc
      | update_pc       => Some sep_contract_update_pc
      | read_mem        => Some sep_contract_read_mem
      | write_mem       => Some sep_contract_write_mem
      | perm_to_bits    => Some sep_contract_perm_to_bits
      | perm_from_bits  => Some sep_contract_perm_from_bits
      | is_sub_perm     => Some sep_contract_is_sub_perm
      | is_within_range => Some sep_contract_is_within_range
      | abs             => Some sep_contract_abs
      | exec_jr         => Some sep_contract_exec_jr
      | exec_jalr       => Some sep_contract_exec_jalr
      | exec_j          => Some sep_contract_exec_j
      | exec_jal        => Some sep_contract_exec_jal
      | exec_bnez       => Some sep_contract_exec_bnez
      | exec_mv         => Some sep_contract_exec_mv
      | exec_ld         => Some sep_contract_exec_ld
      | exec_sd         => Some sep_contract_exec_sd
      | exec_lea        => Some sep_contract_exec_lea
      | exec_restrict   => Some sep_contract_exec_restrict
      | exec_restricti  => Some sep_contract_exec_restricti
      | exec_subseg     => Some sep_contract_exec_subseg
      | exec_subsegi    => Some sep_contract_exec_subsegi
      | exec_addi       => Some sep_contract_exec_addi
      | exec_add        => Some sep_contract_exec_add
      | exec_sub        => Some sep_contract_exec_sub
      | exec_slt        => Some sep_contract_exec_slt
      | exec_slti       => Some sep_contract_exec_slti
      | exec_sltu       => Some sep_contract_exec_sltu
      | exec_sltiu      => Some sep_contract_exec_slti
      | exec_isptr      => Some sep_contract_exec_isptr
      | exec_getp       => Some sep_contract_exec_getp
      | exec_getb       => Some sep_contract_exec_getb
      | exec_gete       => Some sep_contract_exec_gete
      | exec_geta       => Some sep_contract_exec_geta
      | exec_fail       => Some sep_contract_exec_fail
      | exec_ret        => Some sep_contract_exec_ret
      | exec_instr      => Some sep_contract_exec_instr
      | exec            => Some sep_contract_exec
      | loop            => Some sep_contract_loop
      end.

  Lemma linted_cenv :
    forall Δ τ (f : Fun Δ τ),
      match CEnv f with
      | Some c => Linted c
      | None   => True
      end.
  Proof. intros ? ? []; try constructor. Qed.

  Definition lemma_open_ptsreg : SepLemma open_ptsreg :=
    {| lemma_logic_variables := [ "reg" ∶ ty_enum regname, "w" ∶ ty_word];
       lemma_patterns        := [term_var "reg"]%arg;
       lemma_precondition    := term_var "reg" ↦r term_var "w";
       lemma_postcondition   :=
         asn_match_enum
           regname (term_var "reg")
           (fun k => match k with
                     | R0 => reg0 ↦ term_var "w"
                     | R1 => reg1 ↦ term_var "w"
                     (* | R2 => reg2 ↦ term_var "w"
                     | R3 => reg3 ↦ term_var "w" *)
                     end)
    |}.

  Definition lemma_safe_move_cursor : SepLemma safe_move_cursor :=
    let Σ : LCtx := ["p" ∶ ty_perm, "b" ∶ ty_addr, "e" ∶ ty_addr, "a" ∶ ty_addr, "a'" ∶ ty_addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a'"] in
    {| lemma_logic_variables := Σ;
       lemma_patterns        := [c', c]%arg;
       lemma_precondition    := asn_csafe c;
       lemma_postcondition   :=
         asn_csafe c ∗
         asn_csafe c';
    |}.

  (*
    @pre c = mkcap(p,b,e,a) ✱ c' = mkcap(p',b,e,a) ✱ csafe(c) ✱ p' ≤ p
    @post csafe(c) ✱ csafe(c')
    unit csafe_sub_perm(c : capability, c' : capability);
   *)
  Definition lemma_safe_sub_perm : SepLemma safe_sub_perm :=
    let Σ : LCtx := ["p" ∶ ty_perm, "p'" ∶ ty_perm, "b" ∶ ty_addr, "e" ∶ ty_addr, "a" ∶ ty_addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p'", term_var "b", term_var "e", term_var "a"] in
    {| lemma_logic_variables := Σ;
       lemma_patterns        := [c', c]%arg;
       lemma_precondition    :=
         asn_csafe c ∗ term_var "p'" <=ₚ term_var "p";
       lemma_postcondition   :=
         asn_csafe c ∗
         asn_csafe c';
    |}.

  (*
    @pre c = mkcap(p,b,e,a) ✱ c' = mkcap(p,b',e',a) ✱ csafe(c) ✱ b ≤ b' ✱ e' ≤ e
    @post csafe(c) ✱ csafe(c')
    unit csafe_within_range(c' : capability, c : capability);
   *)
  Definition lemma_safe_within_range : SepLemma safe_within_range :=
    let Σ : LCtx := ["p" ∶ ty_perm, "b" ∶ ty_addr, "b'" ∶ ty_addr, "e" ∶ ty_addr, "e'" ∶ ty_addr, "a" ∶ ty_addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p", term_var "b'", term_var "e'", term_var "a"] in
    {| lemma_logic_variables := Σ;
       lemma_patterns        := [c', c]%arg;
       lemma_precondition    :=
         asn_csafe c ∗
         asn_dummy c' ∗
         asn_formula
         (formula_bool
            (term_binop binop_and
                        (term_binop binop_le (term_var "b") (term_var "b'"))
                        (term_binop binop_le (term_var "e'") (term_var "e"))));
       lemma_postcondition   :=
         asn_csafe c ∗
         asn_csafe c';
    |}.

  (*
    @pre true
    @post safe(i)
    unit int_safe(i : int);
   *)
  Definition lemma_int_safe : SepLemma int_safe :=
    {| lemma_logic_variables := ["i" ∶ ty_int];
       lemma_patterns        := [term_var "i"]%arg;
       lemma_precondition    := asn_true;
       lemma_postcondition   :=
         asn_safe (term_inl (term_var "i"));
    |}.

  Definition regtag_to_reg (R : RegName) : Reg ty_word :=
    match R with
    | R0 => reg0
    | R1 => reg1
    (* | R2 => reg2
    | R3 => reg3 *)
    end.

  Definition lemma_close_ptsreg (r : RegName) : SepLemma (close_ptsreg r) :=
    {| lemma_logic_variables := ["w" ∶ ty_word];
       lemma_patterns        := env_nil;
       lemma_precondition    := regtag_to_reg r ↦ term_var "w";
       lemma_postcondition   := term_enum regname r ↦r term_var "w"
    |}.

  Definition sep_contract_rM : SepContractFunX rM :=
    {| sep_contract_logic_variables := ["address" ∶ ty_addr, "p" ∶ ty_perm, "b" ∶ ty_addr, "e" ∶ ty_addr];
       sep_contract_localstore      := [term_var "address"]%arg;
       sep_contract_precondition    :=
         asn_csafe (term_record capability
                            [term_var "p",
                             term_var "b",
                             term_var "e",
                             term_var "address"]) ∗
                   term_lit ty_perm R <=ₚ term_var "p" ∗
                   asn_within_bounds (term_var "address") (term_var "b") (term_var "e");
       sep_contract_result          := "rM_result";
       sep_contract_postcondition   :=
         asn_csafe (term_record capability
                            [term_var "p",
                             term_var "b",
                             term_var "e",
                             term_var "address"])
           ∗ asn_safe (term_var "rM_result")
    |}.

  Definition sep_contract_wM : SepContractFunX wM :=
    {| sep_contract_logic_variables := ["address" ∶ ty_addr, "new_value" ∶ ty_memval, "p" ∶ ty_perm, "b" ∶ ty_addr, "e" ∶ ty_addr];
       sep_contract_localstore      := [term_var "address", term_var "new_value"]%arg;
       sep_contract_precondition    :=
         asn_safe (term_var "new_value")
                  ∗ asn_csafe (term_record capability
                                           [term_var "p",
                                            term_var "b",
                                            term_var "e",
                                            term_var "address"])
                  ∗ term_lit ty_perm RW <=ₚ term_var "p"
                  ∗ asn_within_bounds (term_var "address") (term_var "b") (term_var "e");
       sep_contract_result          := "wM_result";
       sep_contract_postcondition   :=
         asn_csafe (term_record capability
                            [term_var "p",
                             term_var "b",
                             term_var "e",
                             term_var "address"])
           ∗ asn_eq (term_var "wM_result") (term_lit ty_unit tt)
    |}.

  Definition sep_contract_dI : SepContractFunX dI :=
    {| sep_contract_logic_variables := ["code" ∶ ty_int];
       sep_contract_localstore      := [term_var "code"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "_";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition lemma_gen_dummy : SepLemma gen_dummy :=
    {| lemma_logic_variables := ["c" ∶ ty_cap];
       lemma_patterns        := [term_var "c"]%arg;
       lemma_precondition    := asn_true;
       lemma_postcondition   := asn_dummy (term_var "c");
    |}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | rM => sep_contract_rM
      | wM => sep_contract_wM
      | dI => sep_contract_dI
      end.

  Definition LEnv : LemmaEnv :=
    fun Δ l =>
      match l with
        | open_ptsreg            => lemma_open_ptsreg
        | close_ptsreg r         => lemma_close_ptsreg r
        | safe_move_cursor       => lemma_safe_move_cursor
        | safe_sub_perm          => lemma_safe_sub_perm
        | safe_within_range      => lemma_safe_within_range
        | int_safe               => lemma_int_safe
        | gen_dummy              => lemma_gen_dummy
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
  Qed.

  Equations(noeqns) simplify_subperm {Σ} (p q : Term Σ ty_perm) : option (List Formula Σ) :=
  | term_lit p | term_lit q := if decide_subperm p q then Some nil else None;
  | term_lit O | q          := Some nil;
  | p          | q          :=
    let ts := env_nil ► (ty_perm ↦ p) ► (ty_perm ↦ q) in
    Some (cons (formula_user subperm ts) nil).

  Definition simplify_user {Σ} (p : 𝑷) : Env (Term Σ) (𝑷_Ty p) -> option (List Formula Σ) :=
    match p with
    | subperm => fun ts =>
                   let (ts,q) := snocView ts in
                   let (ts,p) := snocView ts in
                   simplify_subperm p q
    end.

  Definition simplify_formula {Σ} (fml : Formula Σ) : option (List Formula Σ) :=
    match fml with
    | formula_user p ts => simplify_user p ts
    | _                 => Some (cons fml nil)
    end.

  Import base.
  Definition simplify_all {Σ} (g : Formula Σ -> option (List Formula Σ)) :=
    fix simplify_all (fmls k : List Formula Σ) {struct fmls} : option (List Formula Σ) :=
      match fmls with
      | nil => Some k
      | cons fml0 fmls =>
        ks ← simplify_all fmls k ;
        k0 ← g fml0 ;
        Some (app k0 ks)
      end.

  Definition solver : Solver :=
    fun w fmls => option_map (fun l => existT w (tri_id , l)) (simplify_all simplify_formula fmls nil).
  Definition solver_spec : SolverSpec solver.
  Admitted.

  Definition solver_user : option SoundSolver :=
    Some (exist SolverSpec solver solver_spec).

End MinCapsSymbolicContractKit.

Module MinCapsMutators :=
  Mutators
    MinCapsTermKit
    MinCapsProgramKit
    MinCapsAssertionKit
    MinCapsSymbolicContractKit.
Import MinCapsMutators.
Import SMut.

Local Ltac solve :=
  repeat
    (repeat
       match goal with
       | H: _ /\ _ |- _ => destruct H
       | H: Empty_set |- _ => destruct H
       | |- forall _, _ => cbn [Lit snd]; intro
       | |- False \/ _ =>  right
       | |- _ \/ False =>  left
       | |- _ \/ exists _, _ =>  left (* avoid existentials, bit fishy but fine for now *)
       | |- _ /\ _ => constructor
       | |- VerificationCondition _ =>
         constructor;
         cbv [SPath.safe env_remove env_lookup inctx_case_snoc eval_binop is_true
              inst instantiate_term instantiate_formula inst_term inst_formula Env_rect];
         cbn
       | |- Obligation _ _ _ => constructor; cbn
       | |- Debug _ _ => constructor
       | |- Debug _ True \/ _ => left
       | |- (_ \/ _) \/ _ => rewrite or_assoc
       | |- context[Z.leb ?x ?y] =>
         destruct (Z.leb_spec x y)
       end;
     cbn [List.length andb is_true Lit snd];
     subst; try congruence; try lia;
     auto
    ).

Local Notation "r '↦' t" := (chunk_ptsreg r t) (at level 100, only printing).
Local Notation "r '↦r' t" := (chunk_user ptsreg (env_nil ► (ty_enum regname ↦ r) ► (ty_word ↦ t))) (at level 100, only printing).
Local Notation "a '↦m' t" := (chunk_user ptsto (env_nil ► (ty_addr ↦ a) ► (ty_int ↦ t))) (at level 100, only printing).
Local Notation "p '∗' q" := (asn_sep p q) (at level 150).
Local Notation safew w := (chunk_user safe (env_nil ► (ty_word ↦ w))).
Local Notation asn_csafe c := (asn_chunk (chunk_user safe (env_nil ► (ty_word ↦ (term_inr c))))).
Local Notation asn_dummy c := (asn_chunk (chunk_user dummy (env_nil ► (ty_cap ↦ c)))).
Local Notation asn_match_cap c p b e a asn :=
(asn_match_record
    capability c
    (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
    "cap_permission" p)
    "cap_begin" b)
    "cap_end" e)
    "cap_cursor" a)
    asn).
Local Notation asn_within_bounds a b e :=
  (asn_formula (formula_bool (term_binop binop_and
                                         (term_binop binop_le b a)
                                         (term_binop binop_le a e)))).

Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => ValidContractReflect c (Pi f)
  (* | Some c => SMut.ValidContract c (Pi f) *)
  | None => False
  end.

Lemma ValidContractsFun : forall {Δ τ} (f : Fun Δ τ),
    ValidContract f.
Proof.
  destruct f; reflexivity.
Qed.

(*
Ltac debug_satisfy_forget_post :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let x := fresh "POST" in
    generalize P; intros x
  end.

Ltac debug_satisfy_remember_post :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let x := fresh "POST" in
    remember P as x
  end.

Ltac debug_satisfy_eval_cbn_inputs :=
  match goal with
  | |- outcome_satisfy (?f ?Σ ?ζ ?s) ?P =>
    let Σ' := eval cbn in Σ in
    let ζ' := eval cbn in ζ in
    let s' := eval cbn in s in
    change_no_check (outcome_satisfy (f Σ' ζ' s') P)
  end.

Ltac debug_satisfy_eval_cbv :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let o' := eval cbv - [NamedEnv Lit Error] in o in
    change_no_check (outcome_satisfy o' P); cbn [outcome_satisfy]
  end.

Close Scope exp.
Close Scope env.

Definition debug_config : Config :=
  {| config_debug_function _ _ f :=
       match f with
       | read_mem => true
       | _        => false
       end
  |}.
*)
