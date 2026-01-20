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

ROCQ_compile="rocq compile -Q ../theories Tableaux"

# Check if ROCQ is installed
if ! command -v rocq &>/dev/null; then
  error "ROCQ is not installed."
  info "Please follow the installation instructions in INSTALL.md"
  exit 1
fi

# Check if TableauxRocq is compiled
echo -n "From Tableaux Require Import All." > test_compile.v
if $ROCQ_compile test_compile.v; then
	rm -rf test_compile.v*
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
bench_results=$(pwd)/results
repo_token=$1

clone_and_make() {
	if [[ ! -z "$repo_token" ]]; then
		git fetch --unshallow
	fi

	current_commit=$(git rev-parse HEAD)
	old_commit=$(git merge-base origin/master $current_commit)

	action "Cloning TableauxRocq with commit $old_commit"
	command="git clone git@github.com:jrosain/TableauxRocq.git"

	if [[ ! -z "$repo_token" ]]; then
		command="git clone https://x-access-token:$repo_token@github.com/jrosain/TableauxRocq.git"
	fi

	if $($command $old_TR_name); then
		cd $old_TR_name
		git config --add remote.origin.fetch "+refs/pull/*/head:refs/remotes/origin/pr/*"
		git fetch --all
		git checkout $old_commit

		action "Compiling old TableauxRocq"
		sh configure.sh
		make -f RocqMakefile
		cd devtools
	else
		error "Could not clone TableauxRocq"
		exit 1
	fi
}

compile_with_time() {
	folder=$1
	old_new=$2

	TIMEFORMAT=%R

	if [ -d $folder ]; then
		for f in $(ls $folder/*.v); do
			action "Checking that $f compiles..."
			if $ROCQ_compile $f 2>/dev/null; then
				action "Running benchs for $f"
				test_results=$bench_results/$f.$old_new
				mkdir -p $(dirname $test_results) && touch $test_results
				for i in $(seq 1 $bench_n_compilations); do
					out=$( { time rocq compile -Q ../theories Tableaux $f 2>/dev/null; } 2>&1 )
					echo $out | tr , . >> $test_results
				done
			else
				error "Could not compile $f."
				info "Exiting with error."
				exit 1
			fi
		done
	fi

	unset TIMEFORMAT
}

average() {
	awk 'BEGIN { sum=0; count=0 } { sum += $1; count++ } END { print sum/count }' $1
}

make_results_summary() {
	summary=$bench_results/summary
	touch $summary
	echo -e "File\t Diff.\t Avg. (new)\t Avg. (old)" >> $summary
	for f in $(find $bench_results -type f -name "*.new"); do
		f_name=${f%.new}
		f_old=$f_name.old
		if [ ! -f $f_old ]; then
			avg=$(average $f)
			echo -e "$(basename $f_name)\t -\t $avg sec.\t -" >> $summary
		else
			avg_new=$(average $f)
			avg_old=$(average $f_old)
			diff=$(echo $avg_old $avg_new | awk '{ print 100 - (($1*100)/$2) }')
			echo -e "$(basename $f_name)\t $diff %\t $avg_new sec.\t $avg_old sec." >> $summary
		fi
	done

	info "Benchs summary:"
	column -t -s $'\t' $summary
	echo ""
}

bench() {
	folder=$1
	current_folder=$(pwd)

	action "Setup benches: cloning old TableauxRocq version"
	mkdir $bench_results
	clone_and_make

	compile_with_time $folder "old"
	cd $current_folder
	info "Running benches for new version"
	compile_with_time $folder "new"
	make_results_summary

	action "Cleanup benches: remove old TableauxRocq version and temporary files"
	rm -rf $old_TR_name
	rm -rf $bench_results
}

compile_with_opt_bench() {
	folder=$1
	should_bench=$2

	if [[ $should_bench = "bench" ]]; then
		bench $folder
	else
		for f in $(ls $folder/*.v); do
			action "ROCQ compile $f"
			if $ROCQ_compile $f 2>/dev/null; then
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

# Compile previous bugs
compile tests

# Run benches
compile_and_bench tests/benchs
