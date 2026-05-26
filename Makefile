.PHONY: clean-encoding-dumps

clean-encoding-dumps:
	@find integration_tests -type d -name encoding_dumps -prune -exec rm -rf {} +
	@echo "Removed integration_tests/*/encoding_dumps"
