CXX ?= g++
CXXFLAGS ?= -O2 -std=c++17 -Wall -Wextra -Wpedantic

.PHONY: all test numerics lean tables
all: numerics
numerics: build/pcd
build/pcd: numerics/pcd.cpp $(wildcard numerics/*.hpp)
	mkdir -p build
	$(CXX) $(CXXFLAGS) numerics/pcd.cpp -o $@
test: build/pcd
	./build/pcd --self-test
	python3 -m unittest discover -s literature -p 'test_*.py'
	python3 scripts/make_tables.py --check
lean:
	@test "$(GITHUB_ACTIONS)" = "true" || { echo 'LEAN_CI_ONLY: Use the Verify Lean and C++ GitHub Actions workflow.'; exit 1; }
	python3 scripts/build_lean.py
tables: build/pcd
	python3 scripts/make_tables.py
