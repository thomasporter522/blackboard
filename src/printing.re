open Lang_printing
open Demo
open Program

let string_of_demo_report(r : demo_check_report) : string = {
    if (r.open_goals == [] && r.errors == []) "Proven!" else
    "Goals:\n\n" ++ String.concat("\n", List.map(string_of_judgment_short, r.open_goals))
    ++ "\n\nErrors:\n\n" ++ String.concat("\n", r.errors)
}

let string_of_report(rs : program_check_report) : string = {
    String.concat("\n----\n", List.map(string_of_demo_report, rs))
}