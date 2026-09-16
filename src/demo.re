open Core
open Core.PartialDerivation

type demo = 
    | Hole
    | Hyp(name)
    | InForm(tm, demo, demo)
    | InElim(tm, demo)
    | Have(name, demo, demo)
    | Suffices(name, demo, demo)
    | TypFormn
    | ArrowForm(demo, demo)
    | Ap(name, tm, tm, demo, demo)
    | ArrowIntro(demo)
    | Obvious

type demo_check_report = {
    open_goals : list(judgment),
    errors : list(string)
}

let report (open_goals : list(judgment), errors : list(string)) : demo_check_report = {
    open_goals, errors
}

let merge_reports(r1 : demo_check_report, r2 : demo_check_report) : demo_check_report = {
    open_goals : r1.open_goals @ r2.open_goals,
    errors : r1.errors @ r2.errors
}

// invariant: the root of returned PD.t is the same as that of the provided one
// invariant: the focused of returned PD.t is the tail of that of the provided one
let rec check_demo(s : t, d : demo) : (t, demo_check_report) = {
    switch(d) {
    | Hole => (skip(s), report([focused(s)],[]))
    | Hyp(x) =>
        let n = index_of_name(ctx_of_judgment(focused(s)), x);
        (hyp(s, n), report([], []))
    | InForm(ty, d1, d2) => 
        let s' = in_formation(s, ty);
        let (s'', r1) = check_demo(s', d1);
        let (s''', r2) = check_demo(s'', d2);
        (s''', merge_reports(r1, r2))
    // | InElim(tm, demo)
    // | Have(name, demo, demo)
    // | Suffices(name, demo, demo)
    // | TypFormn
    // | ArrowForm(demo, demo)
    // | Ap(name, tm, tm, demo, demo)
    | ArrowIntro(d) => {
        let s' = arrow_introduction(s);
        let (s'', r) = check_demo(s', d);
        (s'', r)
    }
    // | Obvious
    | _ => failwith("todo")
    }
}

let check_demo_root(root : judgment, d : demo) : demo_check_report = {
    let (s, r) = check_demo(init(root), d);
    assert(verify(s,root));
    r
}
