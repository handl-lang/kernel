local theorem_classes = {
  theorem = true, lemma = true, proposition = true,
  corollary = true, definition = true, remark = true,
  note = true, proof = true,
}

function Div(el)
  if #el.classes == 0 then return nil end
  local cls = el.classes[1]
  if not theorem_classes[cls] then return nil end
  
  if not (FORMAT:match('latex') or FORMAT:match('pdf')) then return nil end
  
  local title = nil
  local content = el.content
  if #content > 0 and content[1].t == 'Header' then
    title = pandoc.utils.stringify(content[1])
    content = {}
    for i = 2, #el.content do
      content[#content+1] = el.content[i]
    end
  end
  
  local label = el.identifier ~= '' and ('\\label{' .. el.identifier .. '}') or ''
  local begin_str
  if title then
    begin_str = '\\begin{' .. cls .. '}[' .. title .. ']' .. label
  else
    begin_str = '\\begin{' .. cls .. '}' .. label
  end
  
  local result = {}
  result[#result+1] = pandoc.RawBlock('latex', begin_str)
  for _, block in ipairs(content) do
    result[#result+1] = block
  end
  result[#result+1] = pandoc.RawBlock('latex', '\\end{' .. cls .. '}')
  
  return result
end
