open Program 
open Elab
open Demo

let check_surface_program (p : surface_program) : program_check_report = {
    let (p', es) = program_of_surface(Empty, p);
    [{open_goals: [], errors: es, completes: []}] @ check_program(p')
}