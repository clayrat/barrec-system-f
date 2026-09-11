(** * Church-style checking — planned

    Introduce RawChurch, TypeError, [scoped n raw], and [forget].
    The internal checker takes n, a context whose types are scoped at n,
    and raw syntax; Checked packages a type, an intrinsic term, scope
    proofs, and [forget t = raw]. The public entry point is checkClosed.

    Under a type abstraction increment n and lift every context type.
    See plan-systemf.md for the complete proposed contract.
    No checker is implemented in this scaffold. *)

From SystemF.F Require Import Syntax Scope.
