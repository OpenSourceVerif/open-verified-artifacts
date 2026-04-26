.PHONY: verify verify-32-add verify-32-negate verify-64-add verify-64-negate

verify: verify-32-add verify-32-negate verify-64-add verify-64-negate

verify-32-add:
	@echo "=== cnum32_add ==="
	@python z3_verify_cnum32_add.py
	@echo ""

verify-32-negate:
	@echo "=== cnum32_negate ==="
	@python z3_verify_cnum32_negate.py
	@echo ""

verify-64-add:
	@echo "=== cnum64_add ==="
	@python z3_verify_cnum64_add.py
	@echo ""

verify-64-negate:
	@echo "=== cnum64_negate ==="
	@python z3_verify_cnum64_negate.py
	@echo ""
