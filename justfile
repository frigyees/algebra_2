set default-list

# compile full edition
full:
    typst compile main.typ algebra_2.pdf

# compile lecture content only
course:
    typst compile --input edition=course main.typ algebra_2_course.pdf

# compile both editions
c: full course

# watch full edition
wf:
    typst watch main.typ algebra_2.pdf

# watch lecture content only
wc:
    typst watch --input edition=course main.typ algebra_2_course.pdf
