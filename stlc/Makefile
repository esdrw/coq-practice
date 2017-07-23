all: syntax judgments soundness

clean:
	rm -rf *.glob *.vo .*.vo.aux

syntax: syntax.v
	coqc syntax.v

judgments: syntax.vo judgments.v
	coqc judgments.v

soundness: syntax.vo judgments.vo soundness.v
	coqc soundness.v
