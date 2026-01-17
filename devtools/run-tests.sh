#!/bin/bash

# Colors
GREEN="$(tput setaf 2)"
RED="$(tput setaf 1)"
YELLOW="$(tput setaf 3)"
BLUE="$(tput setaf 4)"
SKY_BLUE="$(tput setaf 6)"
RESET="$(tput sgr0)"

# Functions for formatted messages
ok() { echo "${GREEN}[OK]${RESET} $1"; }
error() { echo "${RED}[ERROR]${RESET} $1"; }
warn() { echo "${YELLOW}[WARN]${RESET} $1"; }
info() { echo "${BLUE}[INFO]${RESET} $1"; }
action() { echo "${SKY_BLUE}[ACTION]${RESET} $1"; }

ROCQ_compile() {
	rocq compile -Q ../theories Tableaux $1
}

# Check if ROCQ is installed
if ! command -v rocq &>/dev/null; then
  error "ROCQ is not installed."
  info "Please follow the installation instructions in INSTALL.md"
  exit 1
fi

# Check if TableauxRocq is compiled
echo -n "From Tableaux Require Import All." > test_compile.v
if ROCQ_compile test_compile.v; then
	rm -rf test_compile.vo*
	rm -rf test_compile.glob
else
	info "TableauxRocq has not been compiled. Compiling now..."
	if cd .. && make -f RocqMakefile; then
		ok "Succesfully compiled TableauxRocq."
		cd devtools
	else
		error "Compilation of TableauxRocq has failed."
		info "Please compile the TableauxRocq library."
		exit 1
	fi
fi

# Compile & bench all the files in a folder.
# Enabling benches will fetch the previous version of TableauxRocq, compile
# both version n times, and average out the compilation time.
bench_n_compilations=10
old_TR_name="TR_old"

clone_and_make() {
	current_commit=$(git rev-parse HEAD)
	old_commit=$(git merge-base origin/master $current_commit)

	action "Cloning TableauxRocq with commit $old_commit"

	if git clone git@github.com/jrosain/TableauxRocq.git $old_TR_name; then
		cd $old_TR_name
		git config --add remote.origin.fetch "+refs/pull/*/head:refs/remotes/origin/pr/*"
		git fetch --all
		git checkout $old_commit

		action "Compiling old TableauxRocq"
		make -f RocqMakefile
	else
		error "Could not clone TableauxRocq"
		exit 1
	fi
}

bench() {
	folder=$1
	current_folder=$(pwd)

	action "Setup benches: cloning old TableauxRocq version"
	clone_and_make

	# run benches of old commit
	# run benches of new commit
	# summarise results

	action "Cleanup benches: remove old TableauxRocq version"
	cd current_folder
	rm -rf $old_TR_name
}

compile_with_opt_bench() {
	folder=$1
	should_bench=$2

	if [[ $should_bench = "bench" ]]; then
		bench $folder
	else
		for f in $(ls $folder/*.v); do
			action "ROCQ compile $f"
			if ROCQ_compile $f 2>/dev/null; then
				ok "$f has successfully compiled."
			else
				error "Could not compile $f."
				info "Exiting with error."
				exit 1
			fi
		done
	fi
}

compile() {
	compile_with_opt_bench $1
}

compile_and_bench() {
	compile_with_opt_bench $1 "bench"
}

# Sanity check: compile examples
compile ../examples

# Compile previous bugs
compile tests

# Run benches
compile_and_bench tests/benchs
