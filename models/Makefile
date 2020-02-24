.PHONY: model-check
MODEL_MAKEFILES?= \
	$(foreach file,\
	    $(wildcard *.mk),$(notdir $(file)))

model-check:
	$(foreach n, $(MODEL_MAKEFILES), $(MAKE) -f $(n) &&) true
