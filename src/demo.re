open Core

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

let rec check_demo(d : demo, s : PartialDerivation.t) : (demo_check_report, PartialDerivation.t) = {
    switch(d) {
    | Hole => (report([PartialDerivation.focused(s)],[]), PartialDerivation.skip(s))
    | Hyp(x) => {
        switch(PartialDerivation.focused(s)) {
            | J(c, _) => {
                let n = index_of_name(c, x);
                (report([], []), PartialDerivation.hyp(s, n))
            }
        }
    }
    // | InForm(tm, demo, demo)
    // | InElim(tm, demo)
    // | Have(name, demo, demo)
    // | Suffices(name, demo, demo)
    // | TypFormn
    // | ArrowForm(demo, demo)
    // | Ap(name, tm, tm, demo, demo)
    | ArrowIntro(d) => {
        let s' = PartialDerivation.arrow_introduction(s);
        let (report, s'') = check_demo(d, s');
        (report, s'')
    }
    // | Obvious
    | _ => failwith("todo")
    }
}

let check_demo_root(d : demo, root : judgment) : demo_check_report = 
    fst(check_demo(d, PartialDerivation.init(root)))