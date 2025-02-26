# autograde

A simple command line tool to automatically grade Lean assignments.

## Usage

We assume that the course has a course repository with main folder called `Course` where
`autograde` is listed as a dependency. The corresponding section in the `lakefile.toml` would
look like this:

```toml
[[require]]
name = "autograde"
git = "https://github.com/chrisflav/autograde"
```

Note that `autograde` is setup to use the latest lean version, this might cause a conflict with the
version your `Course` repository is using.

### Input preparation

We assume the data source is a moodle course. In this case, download all assignments
from the moodle website to some folder `input`.

To put the files in the correct form for further processing by `autograde`, run
```
lake exe grade source moodle input assignments
```
where `assignments` is a path of your choice.

### Grading

Also, we assume that the course has a course repository with main folder called `Course`.
Then create a file `Course/Homework.lean` and put your homework exercises in there. Use
the `grade` attribute to mark theorems as exercises. For example:

```lean4
import Autograde.EnvExtensions.GradeAttr

@[grade (config := { points := 2 })]
lemma ex1 (n m : ℕ) : n + m = m + n := by
  omega

@[grade (config := { points := 5 })]
lemma ex2 (n m k : ℕ) : (n + m) * k = k * n + m * k := by
  sorry

@[grade (config := { points := 1000 })]
lemma very_hard : False := by
  sorry
```
Then run
```
lake build Course.Homework
```

To run the grading, do
```
lake exe grade --exercises Course.Homework --directory assignments --workingDirectory Course.Homework
```
This will build all the homework files and then start grading. Make sure that all the homework files
compile!
