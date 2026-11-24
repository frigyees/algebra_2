set default-list

# compile full edition
full:
    typst compile main.typ algebra_2.pdf

# compile lecture content only
course:
    typst compile --input edition=course main.typ algebra_2_course.pdf

# compile both editions
c: full course

# watch either
wf:
    typst watch main.typ algebra_2.pdf

wc:
    typst watch --input edition=course main.typ algebra_2_course.pdf
