local function create_latex_environment(elem, block_class, env_name)
  if elem.classes[1] == block_class then
    print("found attribute " .. block_class)
    local content = elem.text
    local label = ""

    -- Check if there's a label attribute
    if elem.attributes.label then
      label = "\\label{" .. elem.attributes.label .. "}\n"
    end

    -- Parse the content as markdown and extract the blocks
    local parsed_doc = pandoc.read(content, "markdown")
    local parsed_blocks = parsed_doc.blocks

    -- Create the environment with parsed content
    local result = {}

    -- Add opening environment
    table.insert(result, pandoc.RawBlock("latex", "\\begin{" .. env_name .. "}"))

    -- Add label if present
    if label ~= "" then
      table.insert(result, pandoc.RawBlock("latex", "\\label{" .. elem.attributes.label .. "}"))
    end

    -- Add all the parsed markdown blocks
    for _, block in ipairs(parsed_blocks) do
      table.insert(result, block)
    end

    -- Add closing environment
    table.insert(result, pandoc.RawBlock("latex", "\\end{" .. env_name .. "}"))

    return result
  end

  return nil
end

function CodeBlock(elem)
  -- Debug printing
  print("First class:", elem.classes[1])
  print("First class:", elem.classes[1])

  -- Print all attributes
  print("Attributes table contents:")
  for k, v in pairs(elem.attributes) do
    print(string.format("  %s: %s", k, v))
  end
  -- print classes
  print("classes list contents:")
  for k, v in ipairs(elem.classes) do
    print(string.format("  %s: %s", k, v))
  end

  -- Print the raw attr table
  print("Raw attr table:")
  print(pandoc.utils.stringify(elem.attr))

  if elem.attributes.hidden then
    return {}  -- Return empty list to remove the element
  end


  if elem.classes[1] == "tikz" then
    local content = elem.text

    -- Debug print the label and caption we're trying to access
    print("Attempting to access label:", elem.attributes.label)
    print("Attempting to access caption:", elem.attributes.caption)

    content = content:gsub("\\usepackage.-\n", "")
    content = content:gsub("\\begin{document}\n?", "")
    content = content:gsub("\\end{document}\n?", "")

    local label = elem.attributes.label or "fig:tikz-" .. pandoc.sha1(content):sub(1,8)
    local caption = elem.attributes.caption or ""

    -- Print what we ended up using
    print("Final label used:", label)
    print("Final caption used:", caption)

    local figure_content = string.format(
      "\\begin{figure}[htbp]\n\\centering\n%s\n\\caption{%s}\n\\label{%s}\n\\end{figure}",
      content,
      caption,
      label
    )

    return pandoc.RawBlock("latex", figure_content)
  end

  local lemma_result = create_latex_environment(elem, "lemma", "lemma")
  if lemma_result then
    return lemma_result
  end

  local theorem_result = create_latex_environment(elem, "theorem", "thm")
  if theorem_result then
    return theorem_result
  end

  local prop_result = create_latex_environment(elem, "proposition", "prop")
  if prop_result then
    return prop_result
  end
  local lemma_result = create_latex_environment(elem, "postulate", "post")
  if lemma_result then
    return lemma_result
  end
  local defn_result = create_latex_environment(elem, "definition", "defn")
  if defn_result then
    return defn_result
  end
  print("Uknown:", elem.classes[1])
  return elem
end
